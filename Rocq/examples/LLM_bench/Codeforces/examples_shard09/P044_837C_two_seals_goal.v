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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P044_837C_two_seals_lib.
Local Open Scope sac.

(*----- Function fits -----*)

Definition fits_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : (1 <= w1_pre)) (PreH2 : (w1_pre <= 100)) (PreH3 : (1 <= h1_pre)) (PreH4 : (h1_pre <= 100)) (PreH5 : (1 <= w2_pre)) (PreH6 : (w2_pre <= 100)) (PreH7 : (1 <= h2_pre)) (PreH8 : (h2_pre <= 100)) (PreH9 : (1 <= a_pre)) (PreH10 : (a_pre <= 100)) (PreH11 : (1 <= b_pre)) (PreH12 : (b_pre <= 100)) ,
  ((( &( "w1" ) )) # Int  |-> w1_pre)
  **  ((( &( "h1" ) )) # Int  |-> h1_pre)
  **  ((( &( "w2" ) )) # Int  |-> w2_pre)
  **  ((( &( "h2" ) )) # Int  |-> h2_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  “ ((w1_pre + w2_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (w1_pre + w2_pre )) ”
.

Definition fits_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : (h2_pre <= b_pre)) (PreH2 : (h1_pre <= h2_pre)) (PreH3 : ((w1_pre + w2_pre ) <= a_pre)) (PreH4 : (1 <= w1_pre)) (PreH5 : (w1_pre <= 100)) (PreH6 : (1 <= h1_pre)) (PreH7 : (h1_pre <= 100)) (PreH8 : (1 <= w2_pre)) (PreH9 : (w2_pre <= 100)) (PreH10 : (1 <= h2_pre)) (PreH11 : (h2_pre <= 100)) (PreH12 : (1 <= a_pre)) (PreH13 : (a_pre <= 100)) (PreH14 : (1 <= b_pre)) (PreH15 : (b_pre <= 100)) ,
  ((( &( "w1" ) )) # Int  |-> w1_pre)
  **  ((( &( "h1" ) )) # Int  |-> h1_pre)
  **  ((( &( "w2" ) )) # Int  |-> w2_pre)
  **  ((( &( "h2" ) )) # Int  |-> h2_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fits_safety_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : (h1_pre <= b_pre)) (PreH2 : (h1_pre > h2_pre)) (PreH3 : ((w1_pre + w2_pre ) <= a_pre)) (PreH4 : (1 <= w1_pre)) (PreH5 : (w1_pre <= 100)) (PreH6 : (1 <= h1_pre)) (PreH7 : (h1_pre <= 100)) (PreH8 : (1 <= w2_pre)) (PreH9 : (w2_pre <= 100)) (PreH10 : (1 <= h2_pre)) (PreH11 : (h2_pre <= 100)) (PreH12 : (1 <= a_pre)) (PreH13 : (a_pre <= 100)) (PreH14 : (1 <= b_pre)) (PreH15 : (b_pre <= 100)) ,
  ((( &( "w1" ) )) # Int  |-> w1_pre)
  **  ((( &( "h1" ) )) # Int  |-> h1_pre)
  **  ((( &( "w2" ) )) # Int  |-> w2_pre)
  **  ((( &( "h2" ) )) # Int  |-> h2_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fits_safety_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : (h1_pre > b_pre)) (PreH2 : (h1_pre > h2_pre)) (PreH3 : ((w1_pre + w2_pre ) <= a_pre)) (PreH4 : (1 <= w1_pre)) (PreH5 : (w1_pre <= 100)) (PreH6 : (1 <= h1_pre)) (PreH7 : (h1_pre <= 100)) (PreH8 : (1 <= w2_pre)) (PreH9 : (w2_pre <= 100)) (PreH10 : (1 <= h2_pre)) (PreH11 : (h2_pre <= 100)) (PreH12 : (1 <= a_pre)) (PreH13 : (a_pre <= 100)) (PreH14 : (1 <= b_pre)) (PreH15 : (b_pre <= 100)) ,
  ((( &( "w1" ) )) # Int  |-> w1_pre)
  **  ((( &( "h1" ) )) # Int  |-> h1_pre)
  **  ((( &( "w2" ) )) # Int  |-> w2_pre)
  **  ((( &( "h2" ) )) # Int  |-> h2_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  “ ((h1_pre + h2_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (h1_pre + h2_pre )) ”
.

Definition fits_safety_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : (h2_pre > b_pre)) (PreH2 : (h1_pre <= h2_pre)) (PreH3 : ((w1_pre + w2_pre ) <= a_pre)) (PreH4 : (1 <= w1_pre)) (PreH5 : (w1_pre <= 100)) (PreH6 : (1 <= h1_pre)) (PreH7 : (h1_pre <= 100)) (PreH8 : (1 <= w2_pre)) (PreH9 : (w2_pre <= 100)) (PreH10 : (1 <= h2_pre)) (PreH11 : (h2_pre <= 100)) (PreH12 : (1 <= a_pre)) (PreH13 : (a_pre <= 100)) (PreH14 : (1 <= b_pre)) (PreH15 : (b_pre <= 100)) ,
  ((( &( "w1" ) )) # Int  |-> w1_pre)
  **  ((( &( "h1" ) )) # Int  |-> h1_pre)
  **  ((( &( "w2" ) )) # Int  |-> w2_pre)
  **  ((( &( "h2" ) )) # Int  |-> h2_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  “ ((h1_pre + h2_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (h1_pre + h2_pre )) ”
.

Definition fits_safety_wit_6 := 
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : ((w1_pre + w2_pre ) > a_pre)) (PreH2 : (1 <= w1_pre)) (PreH3 : (w1_pre <= 100)) (PreH4 : (1 <= h1_pre)) (PreH5 : (h1_pre <= 100)) (PreH6 : (1 <= w2_pre)) (PreH7 : (w2_pre <= 100)) (PreH8 : (1 <= h2_pre)) (PreH9 : (h2_pre <= 100)) (PreH10 : (1 <= a_pre)) (PreH11 : (a_pre <= 100)) (PreH12 : (1 <= b_pre)) (PreH13 : (b_pre <= 100)) ,
  ((( &( "w1" ) )) # Int  |-> w1_pre)
  **  ((( &( "h1" ) )) # Int  |-> h1_pre)
  **  ((( &( "w2" ) )) # Int  |-> w2_pre)
  **  ((( &( "h2" ) )) # Int  |-> h2_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  “ ((h1_pre + h2_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (h1_pre + h2_pre )) ”
.

Definition fits_safety_wit_7 := 
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : ((h1_pre + h2_pre ) <= b_pre)) (PreH2 : (h2_pre > b_pre)) (PreH3 : (h1_pre <= h2_pre)) (PreH4 : ((w1_pre + w2_pre ) <= a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  ((( &( "w1" ) )) # Int  |-> w1_pre)
  **  ((( &( "h1" ) )) # Int  |-> h1_pre)
  **  ((( &( "w2" ) )) # Int  |-> w2_pre)
  **  ((( &( "h2" ) )) # Int  |-> h2_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  “ False ”
.

Definition fits_safety_wit_8 := 
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : ((h1_pre + h2_pre ) <= b_pre)) (PreH2 : (h1_pre > b_pre)) (PreH3 : (h1_pre > h2_pre)) (PreH4 : ((w1_pre + w2_pre ) <= a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  ((( &( "w1" ) )) # Int  |-> w1_pre)
  **  ((( &( "h1" ) )) # Int  |-> h1_pre)
  **  ((( &( "w2" ) )) # Int  |-> w2_pre)
  **  ((( &( "h2" ) )) # Int  |-> h2_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  “ False ”
.

Definition fits_safety_wit_9 := 
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : (w2_pre <= a_pre)) (PreH2 : (w1_pre <= w2_pre)) (PreH3 : ((h1_pre + h2_pre ) <= b_pre)) (PreH4 : ((w1_pre + w2_pre ) > a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  ((( &( "w1" ) )) # Int  |-> w1_pre)
  **  ((( &( "h1" ) )) # Int  |-> h1_pre)
  **  ((( &( "w2" ) )) # Int  |-> w2_pre)
  **  ((( &( "h2" ) )) # Int  |-> h2_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fits_safety_wit_10 := 
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : (w1_pre <= a_pre)) (PreH2 : (w1_pre > w2_pre)) (PreH3 : ((h1_pre + h2_pre ) <= b_pre)) (PreH4 : ((w1_pre + w2_pre ) > a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  ((( &( "w1" ) )) # Int  |-> w1_pre)
  **  ((( &( "h1" ) )) # Int  |-> h1_pre)
  **  ((( &( "w2" ) )) # Int  |-> w2_pre)
  **  ((( &( "h2" ) )) # Int  |-> h2_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fits_safety_wit_11 := 
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : ((h1_pre + h2_pre ) > b_pre)) (PreH2 : (h1_pre > b_pre)) (PreH3 : (h1_pre > h2_pre)) (PreH4 : ((w1_pre + w2_pre ) <= a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  ((( &( "w1" ) )) # Int  |-> w1_pre)
  **  ((( &( "h1" ) )) # Int  |-> h1_pre)
  **  ((( &( "w2" ) )) # Int  |-> w2_pre)
  **  ((( &( "h2" ) )) # Int  |-> h2_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fits_safety_wit_12 := 
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : ((h1_pre + h2_pre ) > b_pre)) (PreH2 : (h2_pre > b_pre)) (PreH3 : (h1_pre <= h2_pre)) (PreH4 : ((w1_pre + w2_pre ) <= a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  ((( &( "w1" ) )) # Int  |-> w1_pre)
  **  ((( &( "h1" ) )) # Int  |-> h1_pre)
  **  ((( &( "w2" ) )) # Int  |-> w2_pre)
  **  ((( &( "h2" ) )) # Int  |-> h2_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fits_safety_wit_13 := 
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : ((h1_pre + h2_pre ) > b_pre)) (PreH2 : ((w1_pre + w2_pre ) > a_pre)) (PreH3 : (1 <= w1_pre)) (PreH4 : (w1_pre <= 100)) (PreH5 : (1 <= h1_pre)) (PreH6 : (h1_pre <= 100)) (PreH7 : (1 <= w2_pre)) (PreH8 : (w2_pre <= 100)) (PreH9 : (1 <= h2_pre)) (PreH10 : (h2_pre <= 100)) (PreH11 : (1 <= a_pre)) (PreH12 : (a_pre <= 100)) (PreH13 : (1 <= b_pre)) (PreH14 : (b_pre <= 100)) ,
  ((( &( "w1" ) )) # Int  |-> w1_pre)
  **  ((( &( "h1" ) )) # Int  |-> h1_pre)
  **  ((( &( "w2" ) )) # Int  |-> w2_pre)
  **  ((( &( "h2" ) )) # Int  |-> h2_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fits_safety_wit_14 := 
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : (w2_pre > a_pre)) (PreH2 : (w1_pre <= w2_pre)) (PreH3 : ((h1_pre + h2_pre ) <= b_pre)) (PreH4 : ((w1_pre + w2_pre ) > a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  ((( &( "w1" ) )) # Int  |-> w1_pre)
  **  ((( &( "h1" ) )) # Int  |-> h1_pre)
  **  ((( &( "w2" ) )) # Int  |-> w2_pre)
  **  ((( &( "h2" ) )) # Int  |-> h2_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fits_safety_wit_15 := 
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : (w1_pre > a_pre)) (PreH2 : (w1_pre > w2_pre)) (PreH3 : ((h1_pre + h2_pre ) <= b_pre)) (PreH4 : ((w1_pre + w2_pre ) > a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  ((( &( "w1" ) )) # Int  |-> w1_pre)
  **  ((( &( "h1" ) )) # Int  |-> h1_pre)
  **  ((( &( "w2" ) )) # Int  |-> w2_pre)
  **  ((( &( "h2" ) )) # Int  |-> h2_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fits_return_wit_1 := 
(
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : ((h1_pre + h2_pre ) > b_pre)) (PreH2 : (h1_pre > b_pre)) (PreH3 : (h1_pre > h2_pre)) (PreH4 : ((w1_pre + w2_pre ) <= a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ (0 = 0) ” 
  &&  “ ~((FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre )) ”
  &&  emp
) \/
(
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : ((h1_pre + h2_pre ) > b_pre)) (PreH2 : (h1_pre > b_pre)) (PreH3 : (h1_pre > h2_pre)) (PreH4 : ((w1_pre + w2_pre ) <= a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ ~((FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre )) ”
  &&  emp
).

Definition fits_return_wit_1_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : ((h1_pre + h2_pre ) > b_pre)) (PreH2 : (h1_pre > b_pre)) (PreH3 : (h1_pre > h2_pre)) (PreH4 : ((w1_pre + w2_pre ) <= a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  ~((FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre ))
.

Definition fits_return_wit_2 := 
(
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : ((h1_pre + h2_pre ) > b_pre)) (PreH2 : (h2_pre > b_pre)) (PreH3 : (h1_pre <= h2_pre)) (PreH4 : ((w1_pre + w2_pre ) <= a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ (0 = 0) ” 
  &&  “ ~((FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre )) ”
  &&  emp
) \/
(
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : ((h1_pre + h2_pre ) > b_pre)) (PreH2 : (h2_pre > b_pre)) (PreH3 : (h1_pre <= h2_pre)) (PreH4 : ((w1_pre + w2_pre ) <= a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ ~((FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre )) ”
  &&  emp
).

Definition fits_return_wit_2_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : ((h1_pre + h2_pre ) > b_pre)) (PreH2 : (h2_pre > b_pre)) (PreH3 : (h1_pre <= h2_pre)) (PreH4 : ((w1_pre + w2_pre ) <= a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  ~((FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre ))
.

Definition fits_return_wit_3 := 
(
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : ((h1_pre + h2_pre ) > b_pre)) (PreH2 : ((w1_pre + w2_pre ) > a_pre)) (PreH3 : (1 <= w1_pre)) (PreH4 : (w1_pre <= 100)) (PreH5 : (1 <= h1_pre)) (PreH6 : (h1_pre <= 100)) (PreH7 : (1 <= w2_pre)) (PreH8 : (w2_pre <= 100)) (PreH9 : (1 <= h2_pre)) (PreH10 : (h2_pre <= 100)) (PreH11 : (1 <= a_pre)) (PreH12 : (a_pre <= 100)) (PreH13 : (1 <= b_pre)) (PreH14 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ (0 = 0) ” 
  &&  “ ~((FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre )) ”
  &&  emp
) \/
(
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : ((h1_pre + h2_pre ) > b_pre)) (PreH2 : ((w1_pre + w2_pre ) > a_pre)) (PreH3 : (1 <= w1_pre)) (PreH4 : (w1_pre <= 100)) (PreH5 : (1 <= h1_pre)) (PreH6 : (h1_pre <= 100)) (PreH7 : (1 <= w2_pre)) (PreH8 : (w2_pre <= 100)) (PreH9 : (1 <= h2_pre)) (PreH10 : (h2_pre <= 100)) (PreH11 : (1 <= a_pre)) (PreH12 : (a_pre <= 100)) (PreH13 : (1 <= b_pre)) (PreH14 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ ~((FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre )) ”
  &&  emp
).

Definition fits_return_wit_3_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : ((h1_pre + h2_pre ) > b_pre)) (PreH2 : ((w1_pre + w2_pre ) > a_pre)) (PreH3 : (1 <= w1_pre)) (PreH4 : (w1_pre <= 100)) (PreH5 : (1 <= h1_pre)) (PreH6 : (h1_pre <= 100)) (PreH7 : (1 <= w2_pre)) (PreH8 : (w2_pre <= 100)) (PreH9 : (1 <= h2_pre)) (PreH10 : (h2_pre <= 100)) (PreH11 : (1 <= a_pre)) (PreH12 : (a_pre <= 100)) (PreH13 : (1 <= b_pre)) (PreH14 : (b_pre <= 100)) ,
  ~((FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre ))
.

Definition fits_return_wit_4 := 
(
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : (w2_pre > a_pre)) (PreH2 : (w1_pre <= w2_pre)) (PreH3 : ((h1_pre + h2_pre ) <= b_pre)) (PreH4 : ((w1_pre + w2_pre ) > a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ (0 = 0) ” 
  &&  “ ~((FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre )) ”
  &&  emp
) \/
(
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : (w2_pre > a_pre)) (PreH2 : (w1_pre <= w2_pre)) (PreH3 : ((h1_pre + h2_pre ) <= b_pre)) (PreH4 : ((w1_pre + w2_pre ) > a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ ~((FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre )) ”
  &&  emp
).

Definition fits_return_wit_4_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : (w2_pre > a_pre)) (PreH2 : (w1_pre <= w2_pre)) (PreH3 : ((h1_pre + h2_pre ) <= b_pre)) (PreH4 : ((w1_pre + w2_pre ) > a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  ~((FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre ))
.

Definition fits_return_wit_5 := 
(
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : (w1_pre > a_pre)) (PreH2 : (w1_pre > w2_pre)) (PreH3 : ((h1_pre + h2_pre ) <= b_pre)) (PreH4 : ((w1_pre + w2_pre ) > a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ (0 = 0) ” 
  &&  “ ~((FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre )) ”
  &&  emp
) \/
(
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : (w1_pre > a_pre)) (PreH2 : (w1_pre > w2_pre)) (PreH3 : ((h1_pre + h2_pre ) <= b_pre)) (PreH4 : ((w1_pre + w2_pre ) > a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ ~((FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre )) ”
  &&  emp
).

Definition fits_return_wit_5_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : (w1_pre > a_pre)) (PreH2 : (w1_pre > w2_pre)) (PreH3 : ((h1_pre + h2_pre ) <= b_pre)) (PreH4 : ((w1_pre + w2_pre ) > a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  ~((FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre ))
.

Definition fits_return_wit_6 := 
(
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : (w2_pre <= a_pre)) (PreH2 : (w1_pre <= w2_pre)) (PreH3 : ((h1_pre + h2_pre ) <= b_pre)) (PreH4 : ((w1_pre + w2_pre ) > a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ (1 = 1) ” 
  &&  “ (FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre ) ”
  &&  emp
) \/
(
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : (w2_pre <= a_pre)) (PreH2 : (w1_pre <= w2_pre)) (PreH3 : ((h1_pre + h2_pre ) <= b_pre)) (PreH4 : ((w1_pre + w2_pre ) > a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ (FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre ) ”
  &&  emp
).

Definition fits_return_wit_6_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : (w2_pre <= a_pre)) (PreH2 : (w1_pre <= w2_pre)) (PreH3 : ((h1_pre + h2_pre ) <= b_pre)) (PreH4 : ((w1_pre + w2_pre ) > a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  (FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre )
.

Definition fits_return_wit_7 := 
(
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : (w1_pre <= a_pre)) (PreH2 : (w1_pre > w2_pre)) (PreH3 : ((h1_pre + h2_pre ) <= b_pre)) (PreH4 : ((w1_pre + w2_pre ) > a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ (1 = 1) ” 
  &&  “ (FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre ) ”
  &&  emp
) \/
(
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : (w1_pre <= a_pre)) (PreH2 : (w1_pre > w2_pre)) (PreH3 : ((h1_pre + h2_pre ) <= b_pre)) (PreH4 : ((w1_pre + w2_pre ) > a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ (FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre ) ”
  &&  emp
).

Definition fits_return_wit_7_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : (w1_pre <= a_pre)) (PreH2 : (w1_pre > w2_pre)) (PreH3 : ((h1_pre + h2_pre ) <= b_pre)) (PreH4 : ((w1_pre + w2_pre ) > a_pre)) (PreH5 : (1 <= w1_pre)) (PreH6 : (w1_pre <= 100)) (PreH7 : (1 <= h1_pre)) (PreH8 : (h1_pre <= 100)) (PreH9 : (1 <= w2_pre)) (PreH10 : (w2_pre <= 100)) (PreH11 : (1 <= h2_pre)) (PreH12 : (h2_pre <= 100)) (PreH13 : (1 <= a_pre)) (PreH14 : (a_pre <= 100)) (PreH15 : (1 <= b_pre)) (PreH16 : (b_pre <= 100)) ,
  (FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre )
.

Definition fits_return_wit_8 := 
(
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : (h2_pre <= b_pre)) (PreH2 : (h1_pre <= h2_pre)) (PreH3 : ((w1_pre + w2_pre ) <= a_pre)) (PreH4 : (1 <= w1_pre)) (PreH5 : (w1_pre <= 100)) (PreH6 : (1 <= h1_pre)) (PreH7 : (h1_pre <= 100)) (PreH8 : (1 <= w2_pre)) (PreH9 : (w2_pre <= 100)) (PreH10 : (1 <= h2_pre)) (PreH11 : (h2_pre <= 100)) (PreH12 : (1 <= a_pre)) (PreH13 : (a_pre <= 100)) (PreH14 : (1 <= b_pre)) (PreH15 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ (1 = 1) ” 
  &&  “ (FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre ) ”
  &&  emp
) \/
(
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : (h2_pre <= b_pre)) (PreH2 : (h1_pre <= h2_pre)) (PreH3 : ((w1_pre + w2_pre ) <= a_pre)) (PreH4 : (1 <= w1_pre)) (PreH5 : (w1_pre <= 100)) (PreH6 : (1 <= h1_pre)) (PreH7 : (h1_pre <= 100)) (PreH8 : (1 <= w2_pre)) (PreH9 : (w2_pre <= 100)) (PreH10 : (1 <= h2_pre)) (PreH11 : (h2_pre <= 100)) (PreH12 : (1 <= a_pre)) (PreH13 : (a_pre <= 100)) (PreH14 : (1 <= b_pre)) (PreH15 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ (FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre ) ”
  &&  emp
).

Definition fits_return_wit_8_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : (h2_pre <= b_pre)) (PreH2 : (h1_pre <= h2_pre)) (PreH3 : ((w1_pre + w2_pre ) <= a_pre)) (PreH4 : (1 <= w1_pre)) (PreH5 : (w1_pre <= 100)) (PreH6 : (1 <= h1_pre)) (PreH7 : (h1_pre <= 100)) (PreH8 : (1 <= w2_pre)) (PreH9 : (w2_pre <= 100)) (PreH10 : (1 <= h2_pre)) (PreH11 : (h2_pre <= 100)) (PreH12 : (1 <= a_pre)) (PreH13 : (a_pre <= 100)) (PreH14 : (1 <= b_pre)) (PreH15 : (b_pre <= 100)) ,
  (FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre )
.

Definition fits_return_wit_9 := 
(
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : (h1_pre <= b_pre)) (PreH2 : (h1_pre > h2_pre)) (PreH3 : ((w1_pre + w2_pre ) <= a_pre)) (PreH4 : (1 <= w1_pre)) (PreH5 : (w1_pre <= 100)) (PreH6 : (1 <= h1_pre)) (PreH7 : (h1_pre <= 100)) (PreH8 : (1 <= w2_pre)) (PreH9 : (w2_pre <= 100)) (PreH10 : (1 <= h2_pre)) (PreH11 : (h2_pre <= 100)) (PreH12 : (1 <= a_pre)) (PreH13 : (a_pre <= 100)) (PreH14 : (1 <= b_pre)) (PreH15 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ (1 = 1) ” 
  &&  “ (FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre ) ”
  &&  emp
) \/
(
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : (h1_pre <= b_pre)) (PreH2 : (h1_pre > h2_pre)) (PreH3 : ((w1_pre + w2_pre ) <= a_pre)) (PreH4 : (1 <= w1_pre)) (PreH5 : (w1_pre <= 100)) (PreH6 : (1 <= h1_pre)) (PreH7 : (h1_pre <= 100)) (PreH8 : (1 <= w2_pre)) (PreH9 : (w2_pre <= 100)) (PreH10 : (1 <= h2_pre)) (PreH11 : (h2_pre <= 100)) (PreH12 : (1 <= a_pre)) (PreH13 : (a_pre <= 100)) (PreH14 : (1 <= b_pre)) (PreH15 : (b_pre <= 100)) ,
  TT && emp 
|--
  “ (FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre ) ”
  &&  emp
).

Definition fits_return_wit_9_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (h2_pre: Z) (w2_pre: Z) (h1_pre: Z) (w1_pre: Z) (PreH1 : (h1_pre <= b_pre)) (PreH2 : (h1_pre > h2_pre)) (PreH3 : ((w1_pre + w2_pre ) <= a_pre)) (PreH4 : (1 <= w1_pre)) (PreH5 : (w1_pre <= 100)) (PreH6 : (1 <= h1_pre)) (PreH7 : (h1_pre <= 100)) (PreH8 : (1 <= w2_pre)) (PreH9 : (w2_pre <= 100)) (PreH10 : (1 <= h2_pre)) (PreH11 : (h2_pre <= 100)) (PreH12 : (1 <= a_pre)) (PreH13 : (a_pre <= 100)) (PreH14 : (1 <= b_pre)) (PreH15 : (b_pre <= 100)) ,
  (FitsDims w1_pre h1_pre w2_pre h2_pre a_pre b_pre )
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (xs_spec: (@list Z)) (ys_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (1 <= (fst (paper)))) (PreH2 : ((fst (paper)) <= 100)) (PreH3 : (1 <= (snd (paper)))) (PreH4 : ((snd (paper)) <= 100)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((((1 <= (fst ((Znth i seals __default__Prod_Z_Z)))) /\ ((fst ((Znth i seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth i seals __default__Prod_Z_Z))))) /\ ((snd ((Znth i seals __default__Prod_Z_Z))) <= 100)))) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec)) = n_pre)) (PreH12 : ((Zlength (ys_spec)) = n_pre)) (PreH13 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((Znth i_2 xs_spec 0) = (fst ((Znth i_2 seals __default__Prod_Z_Z)))) /\ ((Znth i_2 ys_spec 0) = (snd ((Znth i_2 seals __default__Prod_Z_Z))))))) ,
  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (xs_spec: (@list Z)) (ys_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (1 <= (fst (paper)))) (PreH2 : ((fst (paper)) <= 100)) (PreH3 : (1 <= (snd (paper)))) (PreH4 : ((snd (paper)) <= 100)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((((1 <= (fst ((Znth i seals __default__Prod_Z_Z)))) /\ ((fst ((Znth i seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth i seals __default__Prod_Z_Z))))) /\ ((snd ((Znth i seals __default__Prod_Z_Z))) <= 100)))) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec)) = n_pre)) (PreH12 : ((Zlength (ys_spec)) = n_pre)) (PreH13 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((Znth i_2 xs_spec 0) = (fst ((Znth i_2 seals __default__Prod_Z_Z)))) /\ ((Znth i_2 ys_spec 0) = (snd ((Znth i_2 seals __default__Prod_Z_Z))))))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |-> 0)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec)) = n_pre)) (PreH12 : ((Zlength (ys_spec)) = n_pre)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= best)) (PreH17 : (best <= 20000)) (PreH18 : (BestBefore paper seals i (i + 1 ) 0 0 best )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec)) = n_pre)) (PreH12 : ((Zlength (ys_spec)) = n_pre)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= best)) (PreH17 : (best <= 20000)) (PreH18 : (BestBefore paper seals i (i + 1 ) 0 0 best )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (j < n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec)) = n_pre)) (PreH12 : ((Zlength (ys_spec)) = n_pre)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((i + 1 ) <= j)) (PreH17 : (j <= n_pre)) (PreH18 : (0 <= best)) (PreH19 : (best <= 20000)) (PreH20 : (BestBefore paper seals i j 0 0 best )) ,
  ((( &( "ri" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_6 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (1 <= (fst (paper)))) (PreH2 : ((fst (paper)) <= 100)) (PreH3 : (1 <= (snd (paper)))) (PreH4 : ((snd (paper)) <= 100)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : ((fst (paper)) = a_pre)) (PreH8 : ((snd (paper)) = b_pre)) (PreH9 : (n_pre = (Zlength (seals)))) (PreH10 : ((Zlength (xs_spec)) = n_pre)) (PreH11 : ((Zlength (ys_spec)) = n_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH13 : (0 <= i)) (PreH14 : (i < j)) (PreH15 : (j < n_pre)) (PreH16 : (0 <= ri)) (PreH17 : (ri <= 2)) (PreH18 : (0 <= best)) (PreH19 : (best <= 20000)) (PreH20 : (BestBefore paper seals i j ri 0 best )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_7 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (ri < 2)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec)) = n_pre)) (PreH12 : ((Zlength (ys_spec)) = n_pre)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i < j)) (PreH16 : (j < n_pre)) (PreH17 : (0 <= ri)) (PreH18 : (ri <= 2)) (PreH19 : (0 <= best)) (PreH20 : (best <= 20000)) (PreH21 : (BestBefore paper seals i j ri 0 best )) ,
  ((( &( "rj" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_8 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (1 <= (fst (paper)))) (PreH2 : ((fst (paper)) <= 100)) (PreH3 : (1 <= (snd (paper)))) (PreH4 : ((snd (paper)) <= 100)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : ((fst (paper)) = a_pre)) (PreH8 : ((snd (paper)) = b_pre)) (PreH9 : (n_pre = (Zlength (seals)))) (PreH10 : ((Zlength (xs_spec)) = n_pre)) (PreH11 : ((Zlength (ys_spec)) = n_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH13 : (0 <= i)) (PreH14 : (i < j)) (PreH15 : (j < n_pre)) (PreH16 : (0 <= ri)) (PreH17 : (ri < 2)) (PreH18 : (0 <= rj)) (PreH19 : (rj <= 2)) (PreH20 : (0 <= best)) (PreH21 : (best <= 20000)) (PreH22 : (BestBefore paper seals i j ri rj best )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_9 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (ri = 0)) (PreH2 : (ri <> 0)) (PreH3 : (rj < 2)) (PreH4 : (1 <= (fst (paper)))) (PreH5 : ((fst (paper)) <= 100)) (PreH6 : (1 <= (snd (paper)))) (PreH7 : ((snd (paper)) <= 100)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((fst (paper)) = a_pre)) (PreH11 : ((snd (paper)) = b_pre)) (PreH12 : (n_pre = (Zlength (seals)))) (PreH13 : ((Zlength (xs_spec)) = n_pre)) (PreH14 : ((Zlength (ys_spec)) = n_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH16 : (0 <= i)) (PreH17 : (i < j)) (PreH18 : (j < n_pre)) (PreH19 : (0 <= ri)) (PreH20 : (ri < 2)) (PreH21 : (0 <= rj)) (PreH22 : (rj <= 2)) (PreH23 : (0 <= best)) (PreH24 : (best <= 20000)) (PreH25 : (BestBefore paper seals i j ri rj best )) ,
  ((( &( "h1" ) )) # Int  |->_)
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full x_pre n_pre xs_spec )
|--
  “ False ”
.

Definition solver_safety_wit_10 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (ri <> 0)) (PreH2 : (ri = 0)) (PreH3 : (rj < 2)) (PreH4 : (1 <= (fst (paper)))) (PreH5 : ((fst (paper)) <= 100)) (PreH6 : (1 <= (snd (paper)))) (PreH7 : ((snd (paper)) <= 100)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((fst (paper)) = a_pre)) (PreH11 : ((snd (paper)) = b_pre)) (PreH12 : (n_pre = (Zlength (seals)))) (PreH13 : ((Zlength (xs_spec)) = n_pre)) (PreH14 : ((Zlength (ys_spec)) = n_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH16 : (0 <= i)) (PreH17 : (i < j)) (PreH18 : (j < n_pre)) (PreH19 : (0 <= ri)) (PreH20 : (ri < 2)) (PreH21 : (0 <= rj)) (PreH22 : (rj <= 2)) (PreH23 : (0 <= best)) (PreH24 : (best <= 20000)) (PreH25 : (BestBefore paper seals i j ri rj best )) ,
  ((( &( "h1" ) )) # Int  |->_)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full y_pre n_pre ys_spec )
|--
  “ False ”
.

Definition solver_safety_wit_11 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (rj = 0)) (PreH2 : (rj <> 0)) (PreH3 : (ri <> 0)) (PreH4 : (ri <> 0)) (PreH5 : (rj < 2)) (PreH6 : (1 <= (fst (paper)))) (PreH7 : ((fst (paper)) <= 100)) (PreH8 : (1 <= (snd (paper)))) (PreH9 : ((snd (paper)) <= 100)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : ((fst (paper)) = a_pre)) (PreH13 : ((snd (paper)) = b_pre)) (PreH14 : (n_pre = (Zlength (seals)))) (PreH15 : ((Zlength (xs_spec)) = n_pre)) (PreH16 : ((Zlength (ys_spec)) = n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH18 : (0 <= i)) (PreH19 : (i < j)) (PreH20 : (j < n_pre)) (PreH21 : (0 <= ri)) (PreH22 : (ri < 2)) (PreH23 : (0 <= rj)) (PreH24 : (rj <= 2)) (PreH25 : (0 <= best)) (PreH26 : (best <= 20000)) (PreH27 : (BestBefore paper seals i j ri rj best )) ,
  ((( &( "h2" ) )) # Int  |->_)
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ False ”
.

Definition solver_safety_wit_12 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (rj <> 0)) (PreH2 : (rj = 0)) (PreH3 : (ri <> 0)) (PreH4 : (ri <> 0)) (PreH5 : (rj < 2)) (PreH6 : (1 <= (fst (paper)))) (PreH7 : ((fst (paper)) <= 100)) (PreH8 : (1 <= (snd (paper)))) (PreH9 : ((snd (paper)) <= 100)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : ((fst (paper)) = a_pre)) (PreH13 : ((snd (paper)) = b_pre)) (PreH14 : (n_pre = (Zlength (seals)))) (PreH15 : ((Zlength (xs_spec)) = n_pre)) (PreH16 : ((Zlength (ys_spec)) = n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH18 : (0 <= i)) (PreH19 : (i < j)) (PreH20 : (j < n_pre)) (PreH21 : (0 <= ri)) (PreH22 : (ri < 2)) (PreH23 : (0 <= rj)) (PreH24 : (rj <= 2)) (PreH25 : (0 <= best)) (PreH26 : (best <= 20000)) (PreH27 : (BestBefore paper seals i j ri rj best )) ,
  ((( &( "h2" ) )) # Int  |->_)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ False ”
.

Definition solver_safety_wit_13 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (rj = 0)) (PreH2 : (rj <> 0)) (PreH3 : (ri = 0)) (PreH4 : (ri = 0)) (PreH5 : (rj < 2)) (PreH6 : (1 <= (fst (paper)))) (PreH7 : ((fst (paper)) <= 100)) (PreH8 : (1 <= (snd (paper)))) (PreH9 : ((snd (paper)) <= 100)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : ((fst (paper)) = a_pre)) (PreH13 : ((snd (paper)) = b_pre)) (PreH14 : (n_pre = (Zlength (seals)))) (PreH15 : ((Zlength (xs_spec)) = n_pre)) (PreH16 : ((Zlength (ys_spec)) = n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH18 : (0 <= i)) (PreH19 : (i < j)) (PreH20 : (j < n_pre)) (PreH21 : (0 <= ri)) (PreH22 : (ri < 2)) (PreH23 : (0 <= rj)) (PreH24 : (rj <= 2)) (PreH25 : (0 <= best)) (PreH26 : (best <= 20000)) (PreH27 : (BestBefore paper seals i j ri rj best )) ,
  ((( &( "h2" ) )) # Int  |->_)
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ False ”
.

Definition solver_safety_wit_14 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (rj <> 0)) (PreH2 : (rj = 0)) (PreH3 : (ri = 0)) (PreH4 : (ri = 0)) (PreH5 : (rj < 2)) (PreH6 : (1 <= (fst (paper)))) (PreH7 : ((fst (paper)) <= 100)) (PreH8 : (1 <= (snd (paper)))) (PreH9 : ((snd (paper)) <= 100)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : ((fst (paper)) = a_pre)) (PreH13 : ((snd (paper)) = b_pre)) (PreH14 : (n_pre = (Zlength (seals)))) (PreH15 : ((Zlength (xs_spec)) = n_pre)) (PreH16 : ((Zlength (ys_spec)) = n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH18 : (0 <= i)) (PreH19 : (i < j)) (PreH20 : (j < n_pre)) (PreH21 : (0 <= ri)) (PreH22 : (ri < 2)) (PreH23 : (0 <= rj)) (PreH24 : (rj <= 2)) (PreH25 : (0 <= best)) (PreH26 : (best <= 20000)) (PreH27 : (BestBefore paper seals i j ri rj best )) ,
  ((( &( "h2" ) )) # Int  |->_)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ False ”
.

Definition solver_safety_wit_15 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval = 0)) ,
  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ False ”
.

Definition solver_safety_wit_16 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval = 0)) ,
  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ False ”
.

Definition solver_safety_wit_17 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval = 0)) ,
  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ False ”
.

Definition solver_safety_wit_18 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval = 0)) ,
  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ False ”
.

Definition solver_safety_wit_19 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 0)) (PreH2 : ~((FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre ))) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ False ”
.

Definition solver_safety_wit_20 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 0)) (PreH2 : ~((FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre ))) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ False ”
.

Definition solver_safety_wit_21 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 0)) (PreH2 : ~((FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre ))) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ False ”
.

Definition solver_safety_wit_22 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 0)) (PreH2 : ~((FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre ))) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ False ”
.

Definition solver_safety_wit_23 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((((Znth i ys_spec 0) * (Znth i xs_spec 0) ) + ((Znth j ys_spec 0) * (Znth j xs_spec 0) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth i ys_spec 0) * (Znth i xs_spec 0) ) + ((Znth j ys_spec 0) * (Znth j xs_spec 0) ) )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((((Znth i ys_spec 0) * (Znth i xs_spec 0) ) + ((Znth j ys_spec 0) * (Znth j xs_spec 0) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth i ys_spec 0) * (Znth i xs_spec 0) ) + ((Znth j ys_spec 0) * (Znth j xs_spec 0) ) )) ”
).

Definition solver_safety_wit_23_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((((Znth i ys_spec 0) * (Znth i xs_spec 0) ) + ((Znth j ys_spec 0) * (Znth j xs_spec 0) ) ) <= INT_MAX) ”
.

Definition solver_safety_wit_23_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((INT_MIN) <= (((Znth i ys_spec 0) * (Znth i xs_spec 0) ) + ((Znth j ys_spec 0) * (Znth j xs_spec 0) ) )) ”
.

Definition solver_safety_wit_24 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth j ys_spec 0) * (Znth j xs_spec 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth j ys_spec 0) * (Znth j xs_spec 0) )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth j ys_spec 0) * (Znth j xs_spec 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth j ys_spec 0) * (Znth j xs_spec 0) )) ”
).

Definition solver_safety_wit_24_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth j ys_spec 0) * (Znth j xs_spec 0) ) <= INT_MAX) ”
.

Definition solver_safety_wit_24_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((INT_MIN) <= ((Znth j ys_spec 0) * (Znth j xs_spec 0) )) ”
.

Definition solver_safety_wit_25 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth i ys_spec 0) * (Znth i xs_spec 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i ys_spec 0) * (Znth i xs_spec 0) )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth i ys_spec 0) * (Znth i xs_spec 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i ys_spec 0) * (Znth i xs_spec 0) )) ”
).

Definition solver_safety_wit_25_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth i ys_spec 0) * (Znth i xs_spec 0) ) <= INT_MAX) ”
.

Definition solver_safety_wit_25_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((INT_MIN) <= ((Znth i ys_spec 0) * (Znth i xs_spec 0) )) ”
.

Definition solver_safety_wit_26 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((((Znth i ys_spec 0) * (Znth i xs_spec 0) ) + ((Znth j xs_spec 0) * (Znth j ys_spec 0) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth i ys_spec 0) * (Znth i xs_spec 0) ) + ((Znth j xs_spec 0) * (Znth j ys_spec 0) ) )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((((Znth i ys_spec 0) * (Znth i xs_spec 0) ) + ((Znth j xs_spec 0) * (Znth j ys_spec 0) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth i ys_spec 0) * (Znth i xs_spec 0) ) + ((Znth j xs_spec 0) * (Znth j ys_spec 0) ) )) ”
).

Definition solver_safety_wit_26_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((((Znth i ys_spec 0) * (Znth i xs_spec 0) ) + ((Znth j xs_spec 0) * (Znth j ys_spec 0) ) ) <= INT_MAX) ”
.

Definition solver_safety_wit_26_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((INT_MIN) <= (((Znth i ys_spec 0) * (Znth i xs_spec 0) ) + ((Znth j xs_spec 0) * (Znth j ys_spec 0) ) )) ”
.

Definition solver_safety_wit_27 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth j xs_spec 0) * (Znth j ys_spec 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth j xs_spec 0) * (Znth j ys_spec 0) )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth j xs_spec 0) * (Znth j ys_spec 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth j xs_spec 0) * (Znth j ys_spec 0) )) ”
).

Definition solver_safety_wit_27_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth j xs_spec 0) * (Znth j ys_spec 0) ) <= INT_MAX) ”
.

Definition solver_safety_wit_27_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((INT_MIN) <= ((Znth j xs_spec 0) * (Znth j ys_spec 0) )) ”
.

Definition solver_safety_wit_28 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth i ys_spec 0) * (Znth i xs_spec 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i ys_spec 0) * (Znth i xs_spec 0) )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth i ys_spec 0) * (Znth i xs_spec 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i ys_spec 0) * (Znth i xs_spec 0) )) ”
).

Definition solver_safety_wit_28_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth i ys_spec 0) * (Znth i xs_spec 0) ) <= INT_MAX) ”
.

Definition solver_safety_wit_28_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((INT_MIN) <= ((Znth i ys_spec 0) * (Znth i xs_spec 0) )) ”
.

Definition solver_safety_wit_29 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((((Znth i xs_spec 0) * (Znth i ys_spec 0) ) + ((Znth j ys_spec 0) * (Znth j xs_spec 0) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth i xs_spec 0) * (Znth i ys_spec 0) ) + ((Znth j ys_spec 0) * (Znth j xs_spec 0) ) )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((((Znth i xs_spec 0) * (Znth i ys_spec 0) ) + ((Znth j ys_spec 0) * (Znth j xs_spec 0) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth i xs_spec 0) * (Znth i ys_spec 0) ) + ((Znth j ys_spec 0) * (Znth j xs_spec 0) ) )) ”
).

Definition solver_safety_wit_29_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((((Znth i xs_spec 0) * (Znth i ys_spec 0) ) + ((Znth j ys_spec 0) * (Znth j xs_spec 0) ) ) <= INT_MAX) ”
.

Definition solver_safety_wit_29_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((INT_MIN) <= (((Znth i xs_spec 0) * (Znth i ys_spec 0) ) + ((Znth j ys_spec 0) * (Znth j xs_spec 0) ) )) ”
.

Definition solver_safety_wit_30 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth j ys_spec 0) * (Znth j xs_spec 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth j ys_spec 0) * (Znth j xs_spec 0) )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth j ys_spec 0) * (Znth j xs_spec 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth j ys_spec 0) * (Znth j xs_spec 0) )) ”
).

Definition solver_safety_wit_30_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth j ys_spec 0) * (Znth j xs_spec 0) ) <= INT_MAX) ”
.

Definition solver_safety_wit_30_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((INT_MIN) <= ((Znth j ys_spec 0) * (Znth j xs_spec 0) )) ”
.

Definition solver_safety_wit_31 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth i xs_spec 0) * (Znth i ys_spec 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i xs_spec 0) * (Znth i ys_spec 0) )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth i xs_spec 0) * (Znth i ys_spec 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i xs_spec 0) * (Znth i ys_spec 0) )) ”
).

Definition solver_safety_wit_31_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth i xs_spec 0) * (Znth i ys_spec 0) ) <= INT_MAX) ”
.

Definition solver_safety_wit_31_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((INT_MIN) <= ((Znth i xs_spec 0) * (Znth i ys_spec 0) )) ”
.

Definition solver_safety_wit_32 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((((Znth i xs_spec 0) * (Znth i ys_spec 0) ) + ((Znth j xs_spec 0) * (Znth j ys_spec 0) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth i xs_spec 0) * (Znth i ys_spec 0) ) + ((Znth j xs_spec 0) * (Znth j ys_spec 0) ) )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((((Znth i xs_spec 0) * (Znth i ys_spec 0) ) + ((Znth j xs_spec 0) * (Znth j ys_spec 0) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth i xs_spec 0) * (Znth i ys_spec 0) ) + ((Znth j xs_spec 0) * (Znth j ys_spec 0) ) )) ”
).

Definition solver_safety_wit_32_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((((Znth i xs_spec 0) * (Znth i ys_spec 0) ) + ((Znth j xs_spec 0) * (Znth j ys_spec 0) ) ) <= INT_MAX) ”
.

Definition solver_safety_wit_32_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((INT_MIN) <= (((Znth i xs_spec 0) * (Znth i ys_spec 0) ) + ((Znth j xs_spec 0) * (Znth j ys_spec 0) ) )) ”
.

Definition solver_safety_wit_33 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth j xs_spec 0) * (Znth j ys_spec 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth j xs_spec 0) * (Znth j ys_spec 0) )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth j xs_spec 0) * (Znth j ys_spec 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth j xs_spec 0) * (Znth j ys_spec 0) )) ”
).

Definition solver_safety_wit_33_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth j xs_spec 0) * (Znth j ys_spec 0) ) <= INT_MAX) ”
.

Definition solver_safety_wit_33_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((INT_MIN) <= ((Znth j xs_spec 0) * (Znth j ys_spec 0) )) ”
.

Definition solver_safety_wit_34 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth i xs_spec 0) * (Znth i ys_spec 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i xs_spec 0) * (Znth i ys_spec 0) )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth i xs_spec 0) * (Znth i ys_spec 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i xs_spec 0) * (Znth i ys_spec 0) )) ”
).

Definition solver_safety_wit_34_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth i xs_spec 0) * (Znth i ys_spec 0) ) <= INT_MAX) ”
.

Definition solver_safety_wit_34_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  ((( &( "area" ) )) # Int  |->_)
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((INT_MIN) <= ((Znth i xs_spec 0) * (Znth i ys_spec 0) )) ”
.

Definition solver_safety_wit_35 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (j >= n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec)) = n_pre)) (PreH12 : ((Zlength (ys_spec)) = n_pre)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((i + 1 ) <= j)) (PreH17 : (j <= n_pre)) (PreH18 : (0 <= best)) (PreH19 : (best <= 20000)) (PreH20 : (BestBefore paper seals i j 0 0 best )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_36 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (ri >= 2)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec)) = n_pre)) (PreH12 : ((Zlength (ys_spec)) = n_pre)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i < j)) (PreH16 : (j < n_pre)) (PreH17 : (0 <= ri)) (PreH18 : (ri <= 2)) (PreH19 : (0 <= best)) (PreH20 : (best <= 20000)) (PreH21 : (BestBefore paper seals i j ri 0 best )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_37 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (rj >= 2)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec)) = n_pre)) (PreH12 : ((Zlength (ys_spec)) = n_pre)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i < j)) (PreH16 : (j < n_pre)) (PreH17 : (0 <= ri)) (PreH18 : (ri < 2)) (PreH19 : (0 <= rj)) (PreH20 : (rj <= 2)) (PreH21 : (0 <= best)) (PreH22 : (best <= 20000)) (PreH23 : (BestBefore paper seals i j ri rj best )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
|--
  “ ((ri + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ri + 1 )) ”
.

Definition solver_safety_wit_38 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i ys_spec 0) * (Znth i xs_spec 0) ) + ((Znth j ys_spec 0) * (Znth j xs_spec 0) ) ) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) (PreH4 : (rj <> 0)) (PreH5 : (rj <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (ri <> 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec)) = n_pre)) (PreH19 : ((Zlength (ys_spec)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> (((Znth i ys_spec 0) * (Znth i xs_spec 0) ) + ((Znth j ys_spec 0) * (Znth j xs_spec 0) ) ))
|--
  “ ((rj + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (rj + 1 )) ”
.

Definition solver_safety_wit_39 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i ys_spec 0) * (Znth i xs_spec 0) ) + ((Znth j xs_spec 0) * (Znth j ys_spec 0) ) ) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) (PreH4 : (rj = 0)) (PreH5 : (rj = 0)) (PreH6 : (ri <> 0)) (PreH7 : (ri <> 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec)) = n_pre)) (PreH19 : ((Zlength (ys_spec)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  (IntArray.full y_pre n_pre ys_spec )
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> (((Znth i ys_spec 0) * (Znth i xs_spec 0) ) + ((Znth j xs_spec 0) * (Znth j ys_spec 0) ) ))
|--
  “ ((rj + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (rj + 1 )) ”
.

Definition solver_safety_wit_40 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i xs_spec 0) * (Znth i ys_spec 0) ) + ((Znth j ys_spec 0) * (Znth j xs_spec 0) ) ) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) (PreH4 : (rj <> 0)) (PreH5 : (rj <> 0)) (PreH6 : (ri = 0)) (PreH7 : (ri = 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec)) = n_pre)) (PreH19 : ((Zlength (ys_spec)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> (((Znth i xs_spec 0) * (Znth i ys_spec 0) ) + ((Znth j ys_spec 0) * (Znth j xs_spec 0) ) ))
|--
  “ ((rj + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (rj + 1 )) ”
.

Definition solver_safety_wit_41 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i xs_spec 0) * (Znth i ys_spec 0) ) + ((Znth j xs_spec 0) * (Znth j ys_spec 0) ) ) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) (PreH4 : (rj = 0)) (PreH5 : (rj = 0)) (PreH6 : (ri = 0)) (PreH7 : (ri = 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec)) = n_pre)) (PreH19 : ((Zlength (ys_spec)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  (IntArray.full y_pre n_pre ys_spec )
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> (((Znth i xs_spec 0) * (Znth i ys_spec 0) ) + ((Znth j xs_spec 0) * (Znth j ys_spec 0) ) ))
|--
  “ ((rj + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (rj + 1 )) ”
.

Definition solver_safety_wit_42 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i ys_spec 0) * (Znth i xs_spec 0) ) + ((Znth j ys_spec 0) * (Znth j xs_spec 0) ) ) <= best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) (PreH4 : (rj <> 0)) (PreH5 : (rj <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (ri <> 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec)) = n_pre)) (PreH19 : ((Zlength (ys_spec)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((rj + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (rj + 1 )) ”
.

Definition solver_safety_wit_43 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i ys_spec 0) * (Znth i xs_spec 0) ) + ((Znth j xs_spec 0) * (Znth j ys_spec 0) ) ) <= best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) (PreH4 : (rj = 0)) (PreH5 : (rj = 0)) (PreH6 : (ri <> 0)) (PreH7 : (ri <> 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec)) = n_pre)) (PreH19 : ((Zlength (ys_spec)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  (IntArray.full y_pre n_pre ys_spec )
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((rj + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (rj + 1 )) ”
.

Definition solver_safety_wit_44 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i xs_spec 0) * (Znth i ys_spec 0) ) + ((Znth j ys_spec 0) * (Znth j xs_spec 0) ) ) <= best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) (PreH4 : (rj <> 0)) (PreH5 : (rj <> 0)) (PreH6 : (ri = 0)) (PreH7 : (ri = 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec)) = n_pre)) (PreH19 : ((Zlength (ys_spec)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((rj + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (rj + 1 )) ”
.

Definition solver_safety_wit_45 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i xs_spec 0) * (Znth i ys_spec 0) ) + ((Znth j xs_spec 0) * (Znth j ys_spec 0) ) ) <= best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) (PreH4 : (rj = 0)) (PreH5 : (rj = 0)) (PreH6 : (ri = 0)) (PreH7 : (ri = 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec)) = n_pre)) (PreH19 : ((Zlength (ys_spec)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  (IntArray.full y_pre n_pre ys_spec )
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((rj + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (rj + 1 )) ”
.

Definition solver_safety_wit_46 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 0)) (PreH2 : ~((FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre ))) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval = 0)) ,
  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((rj + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (rj + 1 )) ”
.

Definition solver_safety_wit_47 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 0)) (PreH2 : ~((FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre ))) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval = 0)) ,
  (IntArray.full y_pre n_pre ys_spec )
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((rj + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (rj + 1 )) ”
.

Definition solver_safety_wit_48 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 0)) (PreH2 : ~((FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre ))) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval = 0)) ,
  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((rj + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (rj + 1 )) ”
.

Definition solver_safety_wit_49 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 0)) (PreH2 : ~((FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre ))) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval = 0)) ,
  (IntArray.full y_pre n_pre ys_spec )
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((rj + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (rj + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (xs_spec_2: (@list Z)) (ys_spec_2: (@list Z))  __default__Prod_Z_Z (PreH1 : (1 <= (fst (paper)))) (PreH2 : ((fst (paper)) <= 100)) (PreH3 : (1 <= (snd (paper)))) (PreH4 : ((snd (paper)) <= 100)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((((1 <= (fst ((Znth i seals __default__Prod_Z_Z)))) /\ ((fst ((Znth i seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth i seals __default__Prod_Z_Z))))) /\ ((snd ((Znth i seals __default__Prod_Z_Z))) <= 100)))) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((Znth i_2 xs_spec_2 0) = (fst ((Znth i_2 seals __default__Prod_Z_Z)))) /\ ((Znth i_2 ys_spec_2 0) = (snd ((Znth i_2 seals __default__Prod_Z_Z))))))) ,
  (IntArray.full x_pre n_pre xs_spec_2 )
  **  (IntArray.full y_pre n_pre ys_spec_2 )
|--
  EX (ys_spec: (@list Z))  (xs_spec: (@list Z)) ,
  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 20000) ” 
  &&  “ (BestBefore paper seals 0 (0 + 1 ) 0 0 0 ) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (xs_spec_2: (@list Z)) (ys_spec_2: (@list Z))  __default__Prod_Z_Z (PreH1 : (1 <= (fst (paper)))) (PreH2 : ((fst (paper)) <= 100)) (PreH3 : (1 <= (snd (paper)))) (PreH4 : ((snd (paper)) <= 100)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((((1 <= (fst ((Znth i seals __default__Prod_Z_Z)))) /\ ((fst ((Znth i seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth i seals __default__Prod_Z_Z))))) /\ ((snd ((Znth i seals __default__Prod_Z_Z))) <= 100)))) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((Znth i_2 xs_spec_2 0) = (fst ((Znth i_2 seals __default__Prod_Z_Z)))) /\ ((Znth i_2 ys_spec_2 0) = (snd ((Znth i_2 seals __default__Prod_Z_Z))))))) ,
  TT && emp 
|--
  “ (BestBefore paper seals 0 (0 + 1 ) 0 0 0 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (xs_spec_2: (@list Z)) (ys_spec_2: (@list Z))  __default__Prod_Z_Z (PreH1 : (1 <= (fst (paper)))) (PreH2 : ((fst (paper)) <= 100)) (PreH3 : (1 <= (snd (paper)))) (PreH4 : ((snd (paper)) <= 100)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((((1 <= (fst ((Znth i seals __default__Prod_Z_Z)))) /\ ((fst ((Znth i seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth i seals __default__Prod_Z_Z))))) /\ ((snd ((Znth i seals __default__Prod_Z_Z))) <= 100)))) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((Znth i_2 xs_spec_2 0) = (fst ((Znth i_2 seals __default__Prod_Z_Z)))) /\ ((Znth i_2 ys_spec_2 0) = (snd ((Znth i_2 seals __default__Prod_Z_Z))))))) ,
  (BestBefore paper seals 0 (0 + 1 ) 0 0 0 )
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (xs_spec_2: (@list Z)) (ys_spec_2: (@list Z))  __default__Prod_Z_Z (PreH1 : (1 <= (fst (paper)))) (PreH2 : ((fst (paper)) <= 100)) (PreH3 : (1 <= (snd (paper)))) (PreH4 : ((snd (paper)) <= 100)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((((1 <= (fst ((Znth i seals __default__Prod_Z_Z)))) /\ ((fst ((Znth i seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth i seals __default__Prod_Z_Z))))) /\ ((snd ((Znth i seals __default__Prod_Z_Z))) <= 100)))) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((Znth i_2 xs_spec_2 0) = (fst ((Znth i_2 seals __default__Prod_Z_Z)))) /\ ((Znth i_2 ys_spec_2 0) = (snd ((Znth i_2 seals __default__Prod_Z_Z))))))) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))
.

Definition solver_entail_wit_2 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z))  __default__Prod_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k_2 xs_spec_2 0) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((Znth k_2 ys_spec_2 0) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= best)) (PreH17 : (best <= 20000)) (PreH18 : (BestBefore paper seals i (i + 1 ) 0 0 best )) ,
  (IntArray.full x_pre n_pre xs_spec_2 )
  **  (IntArray.full y_pre n_pre ys_spec_2 )
|--
  EX (ys_spec: (@list Z))  (xs_spec: (@list Z)) ,
  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((i + 1 ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i (i + 1 ) 0 0 best ) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z))  __default__Prod_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k_2 xs_spec_2 0) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((Znth k_2 ys_spec_2 0) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= best)) (PreH17 : (best <= 20000)) (PreH18 : (BestBefore paper seals i (i + 1 ) 0 0 best )) ,
  TT && emp 
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z))  __default__Prod_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k_2 xs_spec_2 0) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((Znth k_2 ys_spec_2 0) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= best)) (PreH17 : (best <= 20000)) (PreH18 : (BestBefore paper seals i (i + 1 ) 0 0 best )) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))
.

Definition solver_entail_wit_3 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z))  __default__Prod_Z_Z (PreH1 : (j < n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k_2 xs_spec_2 0) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((Znth k_2 ys_spec_2 0) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((i + 1 ) <= j)) (PreH17 : (j <= n_pre)) (PreH18 : (0 <= best)) (PreH19 : (best <= 20000)) (PreH20 : (BestBefore paper seals i j 0 0 best )) ,
  (IntArray.full x_pre n_pre xs_spec_2 )
  **  (IntArray.full y_pre n_pre ys_spec_2 )
|--
  EX (ys_spec: (@list Z))  (xs_spec: (@list Z)) ,
  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j 0 0 best ) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z))  __default__Prod_Z_Z (PreH1 : (j < n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k_2 xs_spec_2 0) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((Znth k_2 ys_spec_2 0) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((i + 1 ) <= j)) (PreH17 : (j <= n_pre)) (PreH18 : (0 <= best)) (PreH19 : (best <= 20000)) (PreH20 : (BestBefore paper seals i j 0 0 best )) ,
  TT && emp 
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z))  __default__Prod_Z_Z (PreH1 : (j < n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k_2 xs_spec_2 0) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((Znth k_2 ys_spec_2 0) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((i + 1 ) <= j)) (PreH17 : (j <= n_pre)) (PreH18 : (0 <= best)) (PreH19 : (best <= 20000)) (PreH20 : (BestBefore paper seals i j 0 0 best )) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))
.

Definition solver_entail_wit_4 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z))  __default__Prod_Z_Z (PreH1 : (ri < 2)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k_2 xs_spec_2 0) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((Znth k_2 ys_spec_2 0) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i < j)) (PreH16 : (j < n_pre)) (PreH17 : (0 <= ri)) (PreH18 : (ri <= 2)) (PreH19 : (0 <= best)) (PreH20 : (best <= 20000)) (PreH21 : (BestBefore paper seals i j ri 0 best )) ,
  (IntArray.full x_pre n_pre xs_spec_2 )
  **  (IntArray.full y_pre n_pre ys_spec_2 )
|--
  EX (ys_spec: (@list Z))  (xs_spec: (@list Z)) ,
  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri 0 best ) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z))  __default__Prod_Z_Z (PreH1 : (ri < 2)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k_2 xs_spec_2 0) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((Znth k_2 ys_spec_2 0) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i < j)) (PreH16 : (j < n_pre)) (PreH17 : (0 <= ri)) (PreH18 : (ri <= 2)) (PreH19 : (0 <= best)) (PreH20 : (best <= 20000)) (PreH21 : (BestBefore paper seals i j ri 0 best )) ,
  TT && emp 
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z))  __default__Prod_Z_Z (PreH1 : (ri < 2)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k_2 xs_spec_2 0) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((Znth k_2 ys_spec_2 0) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i < j)) (PreH16 : (j < n_pre)) (PreH17 : (0 <= ri)) (PreH18 : (ri <= 2)) (PreH19 : (0 <= best)) (PreH20 : (best <= 20000)) (PreH21 : (BestBefore paper seals i j ri 0 best )) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))
.

Definition solver_entail_wit_5_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 0)) (PreH2 : ~((FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre ))) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval = 0)) ,
  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
|--
  “ (retval = 0) ” 
  &&  “ ~((FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval = 0) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
.

Definition solver_entail_wit_5_2 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval_5: Z)  __default__Prod_Z_Z (PreH1 : (retval_5 = 1)) (PreH2 : (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval_5 = 0)) ,
  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
|--
  (EX (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ ~((FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval = 0) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0)))
  ||
  (EX (retval_2: Z) ,
  “ (retval_2 = 0) ” 
  &&  “ ~((FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) ” 
  &&  “ (rj = 0) ” 
  &&  “ (rj = 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval_2 = 0) ”
  &&  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0)))
  ||
  (EX (retval_3: Z) ,
  “ (retval_3 = 0) ” 
  &&  “ ~((FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval_3 = 0) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0)))
  ||
  (EX (retval_4: Z) ,
  “ (retval_4 = 0) ” 
  &&  “ ~((FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) ” 
  &&  “ (rj = 0) ” 
  &&  “ (rj = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval_4 = 0) ”
  &&  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0)))
.

Definition solver_entail_wit_5_3 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval_2: Z)  __default__Prod_Z_Z (PreH1 : (retval_2 = 0)) (PreH2 : ~((FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre ))) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval_2 = 0)) ,
  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
|--
  “ (retval_2 = 0) ” 
  &&  “ ~((FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) ” 
  &&  “ (rj = 0) ” 
  &&  “ (rj = 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval_2 = 0) ”
  &&  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
.

Definition solver_entail_wit_5_4 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval_5: Z)  __default__Prod_Z_Z (PreH1 : (retval_5 = 1)) (PreH2 : (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval_5 = 0)) ,
  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
|--
  (EX (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ ~((FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval = 0) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0)))
  ||
  (EX (retval_2: Z) ,
  “ (retval_2 = 0) ” 
  &&  “ ~((FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) ” 
  &&  “ (rj = 0) ” 
  &&  “ (rj = 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval_2 = 0) ”
  &&  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0)))
  ||
  (EX (retval_3: Z) ,
  “ (retval_3 = 0) ” 
  &&  “ ~((FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval_3 = 0) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0)))
  ||
  (EX (retval_4: Z) ,
  “ (retval_4 = 0) ” 
  &&  “ ~((FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) ” 
  &&  “ (rj = 0) ” 
  &&  “ (rj = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval_4 = 0) ”
  &&  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0)))
.

Definition solver_entail_wit_5_5 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval_3: Z)  __default__Prod_Z_Z (PreH1 : (retval_3 = 0)) (PreH2 : ~((FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre ))) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval_3 = 0)) ,
  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
|--
  “ (retval_3 = 0) ” 
  &&  “ ~((FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval_3 = 0) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
.

Definition solver_entail_wit_5_6 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval_5: Z)  __default__Prod_Z_Z (PreH1 : (retval_5 = 1)) (PreH2 : (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval_5 = 0)) ,
  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
|--
  (EX (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ ~((FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval = 0) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0)))
  ||
  (EX (retval_2: Z) ,
  “ (retval_2 = 0) ” 
  &&  “ ~((FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) ” 
  &&  “ (rj = 0) ” 
  &&  “ (rj = 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval_2 = 0) ”
  &&  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0)))
  ||
  (EX (retval_3: Z) ,
  “ (retval_3 = 0) ” 
  &&  “ ~((FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval_3 = 0) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0)))
  ||
  (EX (retval_4: Z) ,
  “ (retval_4 = 0) ” 
  &&  “ ~((FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) ” 
  &&  “ (rj = 0) ” 
  &&  “ (rj = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval_4 = 0) ”
  &&  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0)))
.

Definition solver_entail_wit_5_7 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval_4: Z)  __default__Prod_Z_Z (PreH1 : (retval_4 = 0)) (PreH2 : ~((FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre ))) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval_4 = 0)) ,
  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
|--
  “ (retval_4 = 0) ” 
  &&  “ ~((FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) ” 
  &&  “ (rj = 0) ” 
  &&  “ (rj = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval_4 = 0) ”
  &&  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
.

Definition solver_entail_wit_5_8 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval_5: Z)  __default__Prod_Z_Z (PreH1 : (retval_5 = 1)) (PreH2 : (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval_5 = 0)) ,
  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
|--
  (EX (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ ~((FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval = 0) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0)))
  ||
  (EX (retval_2: Z) ,
  “ (retval_2 = 0) ” 
  &&  “ ~((FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) ” 
  &&  “ (rj = 0) ” 
  &&  “ (rj = 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval_2 = 0) ”
  &&  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0)))
  ||
  (EX (retval_3: Z) ,
  “ (retval_3 = 0) ” 
  &&  “ ~((FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval_3 = 0) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0)))
  ||
  (EX (retval_4: Z) ,
  “ (retval_4 = 0) ” 
  &&  “ ~((FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) ” 
  &&  “ (rj = 0) ” 
  &&  “ (rj = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval_4 = 0) ”
  &&  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0)))
.

Definition solver_entail_wit_6_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval_5: Z)  __default__Prod_Z_Z (PreH1 : (retval_5 = 0)) (PreH2 : ~((FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre ))) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval_5 <> 0)) ,
  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
|--
  (EX (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre ) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval <> 0) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0)))
  ||
  (EX (retval_2: Z) ,
  “ (retval_2 = 1) ” 
  &&  “ (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre ) ” 
  &&  “ (rj = 0) ” 
  &&  “ (rj = 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0)))
  ||
  (EX (retval_3: Z) ,
  “ (retval_3 = 1) ” 
  &&  “ (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre ) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval_3 <> 0) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0)))
  ||
  (EX (retval_4: Z) ,
  “ (retval_4 = 1) ” 
  &&  “ (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre ) ” 
  &&  “ (rj = 0) ” 
  &&  “ (rj = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0)))
.

Definition solver_entail_wit_6_2 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 1)) (PreH2 : (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval <> 0)) ,
  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
|--
  “ (retval = 1) ” 
  &&  “ (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre ) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval <> 0) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
.

Definition solver_entail_wit_6_3 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval_5: Z)  __default__Prod_Z_Z (PreH1 : (retval_5 = 0)) (PreH2 : ~((FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre ))) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval_5 <> 0)) ,
  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
|--
  (EX (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre ) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval <> 0) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0)))
  ||
  (EX (retval_2: Z) ,
  “ (retval_2 = 1) ” 
  &&  “ (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre ) ” 
  &&  “ (rj = 0) ” 
  &&  “ (rj = 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0)))
  ||
  (EX (retval_3: Z) ,
  “ (retval_3 = 1) ” 
  &&  “ (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre ) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval_3 <> 0) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0)))
  ||
  (EX (retval_4: Z) ,
  “ (retval_4 = 1) ” 
  &&  “ (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre ) ” 
  &&  “ (rj = 0) ” 
  &&  “ (rj = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0)))
.

Definition solver_entail_wit_6_4 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval_2: Z)  __default__Prod_Z_Z (PreH1 : (retval_2 = 1)) (PreH2 : (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval_2 <> 0)) ,
  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
|--
  “ (retval_2 = 1) ” 
  &&  “ (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre ) ” 
  &&  “ (rj = 0) ” 
  &&  “ (rj = 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
.

Definition solver_entail_wit_6_5 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval_5: Z)  __default__Prod_Z_Z (PreH1 : (retval_5 = 0)) (PreH2 : ~((FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre ))) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval_5 <> 0)) ,
  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
|--
  (EX (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre ) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval <> 0) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0)))
  ||
  (EX (retval_2: Z) ,
  “ (retval_2 = 1) ” 
  &&  “ (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre ) ” 
  &&  “ (rj = 0) ” 
  &&  “ (rj = 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0)))
  ||
  (EX (retval_3: Z) ,
  “ (retval_3 = 1) ” 
  &&  “ (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre ) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval_3 <> 0) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0)))
  ||
  (EX (retval_4: Z) ,
  “ (retval_4 = 1) ” 
  &&  “ (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre ) ” 
  &&  “ (rj = 0) ” 
  &&  “ (rj = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0)))
.

Definition solver_entail_wit_6_6 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval_3: Z)  __default__Prod_Z_Z (PreH1 : (retval_3 = 1)) (PreH2 : (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre )) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval_3 <> 0)) ,
  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
|--
  “ (retval_3 = 1) ” 
  &&  “ (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre ) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval_3 <> 0) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
.

Definition solver_entail_wit_6_7 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval_5: Z)  __default__Prod_Z_Z (PreH1 : (retval_5 = 0)) (PreH2 : ~((FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre ))) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval_5 <> 0)) ,
  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
|--
  (EX (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre ) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval <> 0) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0)))
  ||
  (EX (retval_2: Z) ,
  “ (retval_2 = 1) ” 
  &&  “ (FitsDims (Znth i ys_spec 0) (Znth i xs_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre ) ” 
  &&  “ (rj = 0) ” 
  &&  “ (rj = 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0)))
  ||
  (EX (retval_3: Z) ,
  “ (retval_3 = 1) ” 
  &&  “ (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j ys_spec 0) (Znth j xs_spec 0) a_pre b_pre ) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval_3 <> 0) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0)))
  ||
  (EX (retval_4: Z) ,
  “ (retval_4 = 1) ” 
  &&  “ (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre ) ” 
  &&  “ (rj = 0) ” 
  &&  “ (rj = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0)))
.

Definition solver_entail_wit_6_8 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z)) (retval_4: Z)  __default__Prod_Z_Z (PreH1 : (retval_4 = 1)) (PreH2 : (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre )) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec)) = n_pre)) (PreH18 : ((Zlength (ys_spec)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval_4 <> 0)) ,
  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
|--
  “ (retval_4 = 1) ” 
  &&  “ (FitsDims (Znth i xs_spec 0) (Znth i ys_spec 0) (Znth j xs_spec 0) (Znth j ys_spec 0) a_pre b_pre ) ” 
  &&  “ (rj = 0) ” 
  &&  “ (rj = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
.

Definition solver_entail_wit_7 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z))  __default__Prod_Z_Z (PreH1 : (j >= n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k_2 xs_spec_2 0) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((Znth k_2 ys_spec_2 0) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((i + 1 ) <= j)) (PreH17 : (j <= n_pre)) (PreH18 : (0 <= best)) (PreH19 : (best <= 20000)) (PreH20 : (BestBefore paper seals i j 0 0 best )) ,
  (IntArray.full x_pre n_pre xs_spec_2 )
  **  (IntArray.full y_pre n_pre ys_spec_2 )
|--
  EX (ys_spec: (@list Z))  (xs_spec: (@list Z)) ,
  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals (i + 1 ) ((i + 1 ) + 1 ) 0 0 best ) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z))  __default__Prod_Z_Z (PreH1 : (j >= n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k_2 xs_spec_2 0) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((Znth k_2 ys_spec_2 0) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((i + 1 ) <= j)) (PreH17 : (j <= n_pre)) (PreH18 : (0 <= best)) (PreH19 : (best <= 20000)) (PreH20 : (BestBefore paper seals i j 0 0 best )) ,
  TT && emp 
|--
  “ (BestBefore paper seals (i + 1 ) ((i + 1 ) + 1 ) 0 0 best ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ”
  &&  emp
).

Definition solver_entail_wit_7_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z))  __default__Prod_Z_Z (PreH1 : (j >= n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k_2 xs_spec_2 0) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((Znth k_2 ys_spec_2 0) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((i + 1 ) <= j)) (PreH17 : (j <= n_pre)) (PreH18 : (0 <= best)) (PreH19 : (best <= 20000)) (PreH20 : (BestBefore paper seals i j 0 0 best )) ,
  (BestBefore paper seals (i + 1 ) ((i + 1 ) + 1 ) 0 0 best )
.

Definition solver_entail_wit_7_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z))  __default__Prod_Z_Z (PreH1 : (j >= n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k_2 xs_spec_2 0) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((Znth k_2 ys_spec_2 0) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : ((i + 1 ) <= j)) (PreH17 : (j <= n_pre)) (PreH18 : (0 <= best)) (PreH19 : (best <= 20000)) (PreH20 : (BestBefore paper seals i j 0 0 best )) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))
.

Definition solver_entail_wit_8 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z))  __default__Prod_Z_Z (PreH1 : (ri >= 2)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k_2 xs_spec_2 0) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((Znth k_2 ys_spec_2 0) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i < j)) (PreH16 : (j < n_pre)) (PreH17 : (0 <= ri)) (PreH18 : (ri <= 2)) (PreH19 : (0 <= best)) (PreH20 : (best <= 20000)) (PreH21 : (BestBefore paper seals i j ri 0 best )) ,
  (IntArray.full x_pre n_pre xs_spec_2 )
  **  (IntArray.full y_pre n_pre ys_spec_2 )
|--
  EX (ys_spec: (@list Z))  (xs_spec: (@list Z)) ,
  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((i + 1 ) <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i (j + 1 ) 0 0 best ) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z))  __default__Prod_Z_Z (PreH1 : (ri >= 2)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k_2 xs_spec_2 0) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((Znth k_2 ys_spec_2 0) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i < j)) (PreH16 : (j < n_pre)) (PreH17 : (0 <= ri)) (PreH18 : (ri <= 2)) (PreH19 : (0 <= best)) (PreH20 : (best <= 20000)) (PreH21 : (BestBefore paper seals i j ri 0 best )) ,
  TT && emp 
|--
  “ (BestBefore paper seals i (j + 1 ) 0 0 best ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ”
  &&  emp
).

Definition solver_entail_wit_8_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z))  __default__Prod_Z_Z (PreH1 : (ri >= 2)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k_2 xs_spec_2 0) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((Znth k_2 ys_spec_2 0) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i < j)) (PreH16 : (j < n_pre)) (PreH17 : (0 <= ri)) (PreH18 : (ri <= 2)) (PreH19 : (0 <= best)) (PreH20 : (best <= 20000)) (PreH21 : (BestBefore paper seals i j ri 0 best )) ,
  (BestBefore paper seals i (j + 1 ) 0 0 best )
.

Definition solver_entail_wit_8_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z))  __default__Prod_Z_Z (PreH1 : (ri >= 2)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k_2 xs_spec_2 0) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((Znth k_2 ys_spec_2 0) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i < j)) (PreH16 : (j < n_pre)) (PreH17 : (0 <= ri)) (PreH18 : (ri <= 2)) (PreH19 : (0 <= best)) (PreH20 : (best <= 20000)) (PreH21 : (BestBefore paper seals i j ri 0 best )) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))
.

Definition solver_entail_wit_9 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z))  __default__Prod_Z_Z (PreH1 : (rj >= 2)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k_2 xs_spec_2 0) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((Znth k_2 ys_spec_2 0) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i < j)) (PreH16 : (j < n_pre)) (PreH17 : (0 <= ri)) (PreH18 : (ri < 2)) (PreH19 : (0 <= rj)) (PreH20 : (rj <= 2)) (PreH21 : (0 <= best)) (PreH22 : (best <= 20000)) (PreH23 : (BestBefore paper seals i j ri rj best )) ,
  (IntArray.full x_pre n_pre xs_spec_2 )
  **  (IntArray.full y_pre n_pre ys_spec_2 )
|--
  EX (ys_spec: (@list Z))  (xs_spec: (@list Z)) ,
  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= (ri + 1 )) ” 
  &&  “ ((ri + 1 ) <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j (ri + 1 ) 0 best ) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z))  __default__Prod_Z_Z (PreH1 : (rj >= 2)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k_2 xs_spec_2 0) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((Znth k_2 ys_spec_2 0) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i < j)) (PreH16 : (j < n_pre)) (PreH17 : (0 <= ri)) (PreH18 : (ri < 2)) (PreH19 : (0 <= rj)) (PreH20 : (rj <= 2)) (PreH21 : (0 <= best)) (PreH22 : (best <= 20000)) (PreH23 : (BestBefore paper seals i j ri rj best )) ,
  TT && emp 
|--
  “ (BestBefore paper seals i j (ri + 1 ) 0 best ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ”
  &&  emp
).

Definition solver_entail_wit_9_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z))  __default__Prod_Z_Z (PreH1 : (rj >= 2)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k_2 xs_spec_2 0) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((Znth k_2 ys_spec_2 0) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i < j)) (PreH16 : (j < n_pre)) (PreH17 : (0 <= ri)) (PreH18 : (ri < 2)) (PreH19 : (0 <= rj)) (PreH20 : (rj <= 2)) (PreH21 : (0 <= best)) (PreH22 : (best <= 20000)) (PreH23 : (BestBefore paper seals i j ri rj best )) ,
  (BestBefore paper seals i j (ri + 1 ) 0 best )
.

Definition solver_entail_wit_9_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z))  __default__Prod_Z_Z (PreH1 : (rj >= 2)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (fst ((Znth k_2 seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k_2 seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k_2 xs_spec_2 0) = (fst ((Znth k_2 seals __default__Prod_Z_Z))))) /\ ((Znth k_2 ys_spec_2 0) = (snd ((Znth k_2 seals __default__Prod_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i < j)) (PreH16 : (j < n_pre)) (PreH17 : (0 <= ri)) (PreH18 : (ri < 2)) (PreH19 : (0 <= rj)) (PreH20 : (rj <= 2)) (PreH21 : (0 <= best)) (PreH22 : (best <= 20000)) (PreH23 : (BestBefore paper seals i j ri rj best )) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))
.

Definition solver_entail_wit_10_1 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i ys_spec_2 0) * (Znth i xs_spec_2 0) ) + ((Znth j ys_spec_2 0) * (Znth j xs_spec_2 0) ) ) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec_2 0) (Znth i xs_spec_2 0) (Znth j ys_spec_2 0) (Znth j xs_spec_2 0) a_pre b_pre )) (PreH4 : (rj <> 0)) (PreH5 : (rj <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (ri <> 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  (IntArray.full x_pre n_pre xs_spec_2 )
  **  (IntArray.full y_pre n_pre ys_spec_2 )
|--
  EX (ys_spec: (@list Z))  (xs_spec: (@list Z)) ,
  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= (rj + 1 )) ” 
  &&  “ ((rj + 1 ) <= 2) ” 
  &&  “ (0 <= (((Znth i ys_spec_2 0) * (Znth i xs_spec_2 0) ) + ((Znth j ys_spec_2 0) * (Znth j xs_spec_2 0) ) )) ” 
  &&  “ ((((Znth i ys_spec_2 0) * (Znth i xs_spec_2 0) ) + ((Znth j ys_spec_2 0) * (Znth j xs_spec_2 0) ) ) <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri (rj + 1 ) (((Znth i ys_spec_2 0) * (Znth i xs_spec_2 0) ) + ((Znth j ys_spec_2 0) * (Znth j xs_spec_2 0) ) ) ) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i ys_spec_2 0) * (Znth i xs_spec_2 0) ) + ((Znth j ys_spec_2 0) * (Znth j xs_spec_2 0) ) ) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec_2 0) (Znth i xs_spec_2 0) (Znth j ys_spec_2 0) (Znth j xs_spec_2 0) a_pre b_pre )) (PreH4 : (rj <> 0)) (PreH5 : (rj <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (ri <> 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  TT && emp 
|--
  “ (BestBefore paper seals i j ri (rj + 1 ) (((Znth i ys_spec_2 0) * (Znth i xs_spec_2 0) ) + ((Znth j ys_spec_2 0) * (Znth j xs_spec_2 0) ) ) ) ” 
  &&  “ ((((Znth i ys_spec_2 0) * (Znth i xs_spec_2 0) ) + ((Znth j ys_spec_2 0) * (Znth j xs_spec_2 0) ) ) <= 20000) ”
  &&  emp
).

Definition solver_entail_wit_10_1_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i ys_spec_2 0) * (Znth i xs_spec_2 0) ) + ((Znth j ys_spec_2 0) * (Znth j xs_spec_2 0) ) ) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec_2 0) (Znth i xs_spec_2 0) (Znth j ys_spec_2 0) (Znth j xs_spec_2 0) a_pre b_pre )) (PreH4 : (rj <> 0)) (PreH5 : (rj <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (ri <> 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  (BestBefore paper seals i j ri (rj + 1 ) (((Znth i ys_spec_2 0) * (Znth i xs_spec_2 0) ) + ((Znth j ys_spec_2 0) * (Znth j xs_spec_2 0) ) ) )
.

Definition solver_entail_wit_10_1_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i ys_spec_2 0) * (Znth i xs_spec_2 0) ) + ((Znth j ys_spec_2 0) * (Znth j xs_spec_2 0) ) ) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec_2 0) (Znth i xs_spec_2 0) (Znth j ys_spec_2 0) (Znth j xs_spec_2 0) a_pre b_pre )) (PreH4 : (rj <> 0)) (PreH5 : (rj <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (ri <> 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  ((((Znth i ys_spec_2 0) * (Znth i xs_spec_2 0) ) + ((Znth j ys_spec_2 0) * (Znth j xs_spec_2 0) ) ) <= 20000)
.

Definition solver_entail_wit_10_2 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i ys_spec_2 0) * (Znth i xs_spec_2 0) ) + ((Znth j xs_spec_2 0) * (Znth j ys_spec_2 0) ) ) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec_2 0) (Znth i xs_spec_2 0) (Znth j xs_spec_2 0) (Znth j ys_spec_2 0) a_pre b_pre )) (PreH4 : (rj = 0)) (PreH5 : (rj = 0)) (PreH6 : (ri <> 0)) (PreH7 : (ri <> 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  (IntArray.full y_pre n_pre ys_spec_2 )
  **  (IntArray.full x_pre n_pre xs_spec_2 )
|--
  EX (ys_spec: (@list Z))  (xs_spec: (@list Z)) ,
  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= (rj + 1 )) ” 
  &&  “ ((rj + 1 ) <= 2) ” 
  &&  “ (0 <= (((Znth i ys_spec_2 0) * (Znth i xs_spec_2 0) ) + ((Znth j xs_spec_2 0) * (Znth j ys_spec_2 0) ) )) ” 
  &&  “ ((((Znth i ys_spec_2 0) * (Znth i xs_spec_2 0) ) + ((Znth j xs_spec_2 0) * (Znth j ys_spec_2 0) ) ) <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri (rj + 1 ) (((Znth i ys_spec_2 0) * (Znth i xs_spec_2 0) ) + ((Znth j xs_spec_2 0) * (Znth j ys_spec_2 0) ) ) ) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i ys_spec_2 0) * (Znth i xs_spec_2 0) ) + ((Znth j xs_spec_2 0) * (Znth j ys_spec_2 0) ) ) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec_2 0) (Znth i xs_spec_2 0) (Znth j xs_spec_2 0) (Znth j ys_spec_2 0) a_pre b_pre )) (PreH4 : (rj = 0)) (PreH5 : (rj = 0)) (PreH6 : (ri <> 0)) (PreH7 : (ri <> 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  TT && emp 
|--
  “ (BestBefore paper seals i j ri (0 + 1 ) (((Znth i ys_spec_2 0) * (Znth i xs_spec_2 0) ) + ((Znth j xs_spec_2 0) * (Znth j ys_spec_2 0) ) ) ) ” 
  &&  “ ((((Znth i ys_spec_2 0) * (Znth i xs_spec_2 0) ) + ((Znth j xs_spec_2 0) * (Znth j ys_spec_2 0) ) ) <= 20000) ”
  &&  emp
).

Definition solver_entail_wit_10_2_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i ys_spec_2 0) * (Znth i xs_spec_2 0) ) + ((Znth j xs_spec_2 0) * (Znth j ys_spec_2 0) ) ) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec_2 0) (Znth i xs_spec_2 0) (Znth j xs_spec_2 0) (Znth j ys_spec_2 0) a_pre b_pre )) (PreH4 : (rj = 0)) (PreH5 : (rj = 0)) (PreH6 : (ri <> 0)) (PreH7 : (ri <> 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  (BestBefore paper seals i j ri (0 + 1 ) (((Znth i ys_spec_2 0) * (Znth i xs_spec_2 0) ) + ((Znth j xs_spec_2 0) * (Znth j ys_spec_2 0) ) ) )
.

Definition solver_entail_wit_10_2_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i ys_spec_2 0) * (Znth i xs_spec_2 0) ) + ((Znth j xs_spec_2 0) * (Znth j ys_spec_2 0) ) ) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec_2 0) (Znth i xs_spec_2 0) (Znth j xs_spec_2 0) (Znth j ys_spec_2 0) a_pre b_pre )) (PreH4 : (rj = 0)) (PreH5 : (rj = 0)) (PreH6 : (ri <> 0)) (PreH7 : (ri <> 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  ((((Znth i ys_spec_2 0) * (Znth i xs_spec_2 0) ) + ((Znth j xs_spec_2 0) * (Znth j ys_spec_2 0) ) ) <= 20000)
.

Definition solver_entail_wit_10_3 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i xs_spec_2 0) * (Znth i ys_spec_2 0) ) + ((Znth j ys_spec_2 0) * (Znth j xs_spec_2 0) ) ) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec_2 0) (Znth i ys_spec_2 0) (Znth j ys_spec_2 0) (Znth j xs_spec_2 0) a_pre b_pre )) (PreH4 : (rj <> 0)) (PreH5 : (rj <> 0)) (PreH6 : (ri = 0)) (PreH7 : (ri = 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  (IntArray.full x_pre n_pre xs_spec_2 )
  **  (IntArray.full y_pre n_pre ys_spec_2 )
|--
  EX (ys_spec: (@list Z))  (xs_spec: (@list Z)) ,
  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= (rj + 1 )) ” 
  &&  “ ((rj + 1 ) <= 2) ” 
  &&  “ (0 <= (((Znth i xs_spec_2 0) * (Znth i ys_spec_2 0) ) + ((Znth j ys_spec_2 0) * (Znth j xs_spec_2 0) ) )) ” 
  &&  “ ((((Znth i xs_spec_2 0) * (Znth i ys_spec_2 0) ) + ((Znth j ys_spec_2 0) * (Znth j xs_spec_2 0) ) ) <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri (rj + 1 ) (((Znth i xs_spec_2 0) * (Znth i ys_spec_2 0) ) + ((Znth j ys_spec_2 0) * (Znth j xs_spec_2 0) ) ) ) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i xs_spec_2 0) * (Znth i ys_spec_2 0) ) + ((Znth j ys_spec_2 0) * (Znth j xs_spec_2 0) ) ) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec_2 0) (Znth i ys_spec_2 0) (Znth j ys_spec_2 0) (Znth j xs_spec_2 0) a_pre b_pre )) (PreH4 : (rj <> 0)) (PreH5 : (rj <> 0)) (PreH6 : (ri = 0)) (PreH7 : (ri = 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  TT && emp 
|--
  “ (BestBefore paper seals i j 0 (rj + 1 ) (((Znth i xs_spec_2 0) * (Znth i ys_spec_2 0) ) + ((Znth j ys_spec_2 0) * (Znth j xs_spec_2 0) ) ) ) ” 
  &&  “ ((((Znth i xs_spec_2 0) * (Znth i ys_spec_2 0) ) + ((Znth j ys_spec_2 0) * (Znth j xs_spec_2 0) ) ) <= 20000) ”
  &&  emp
).

Definition solver_entail_wit_10_3_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i xs_spec_2 0) * (Znth i ys_spec_2 0) ) + ((Znth j ys_spec_2 0) * (Znth j xs_spec_2 0) ) ) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec_2 0) (Znth i ys_spec_2 0) (Znth j ys_spec_2 0) (Znth j xs_spec_2 0) a_pre b_pre )) (PreH4 : (rj <> 0)) (PreH5 : (rj <> 0)) (PreH6 : (ri = 0)) (PreH7 : (ri = 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  (BestBefore paper seals i j 0 (rj + 1 ) (((Znth i xs_spec_2 0) * (Znth i ys_spec_2 0) ) + ((Znth j ys_spec_2 0) * (Znth j xs_spec_2 0) ) ) )
.

Definition solver_entail_wit_10_3_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i xs_spec_2 0) * (Znth i ys_spec_2 0) ) + ((Znth j ys_spec_2 0) * (Znth j xs_spec_2 0) ) ) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec_2 0) (Znth i ys_spec_2 0) (Znth j ys_spec_2 0) (Znth j xs_spec_2 0) a_pre b_pre )) (PreH4 : (rj <> 0)) (PreH5 : (rj <> 0)) (PreH6 : (ri = 0)) (PreH7 : (ri = 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  ((((Znth i xs_spec_2 0) * (Znth i ys_spec_2 0) ) + ((Znth j ys_spec_2 0) * (Znth j xs_spec_2 0) ) ) <= 20000)
.

Definition solver_entail_wit_10_4 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i xs_spec_2 0) * (Znth i ys_spec_2 0) ) + ((Znth j xs_spec_2 0) * (Znth j ys_spec_2 0) ) ) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec_2 0) (Znth i ys_spec_2 0) (Znth j xs_spec_2 0) (Znth j ys_spec_2 0) a_pre b_pre )) (PreH4 : (rj = 0)) (PreH5 : (rj = 0)) (PreH6 : (ri = 0)) (PreH7 : (ri = 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  (IntArray.full y_pre n_pre ys_spec_2 )
  **  (IntArray.full x_pre n_pre xs_spec_2 )
|--
  EX (ys_spec: (@list Z))  (xs_spec: (@list Z)) ,
  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= (rj + 1 )) ” 
  &&  “ ((rj + 1 ) <= 2) ” 
  &&  “ (0 <= (((Znth i xs_spec_2 0) * (Znth i ys_spec_2 0) ) + ((Znth j xs_spec_2 0) * (Znth j ys_spec_2 0) ) )) ” 
  &&  “ ((((Znth i xs_spec_2 0) * (Znth i ys_spec_2 0) ) + ((Znth j xs_spec_2 0) * (Znth j ys_spec_2 0) ) ) <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri (rj + 1 ) (((Znth i xs_spec_2 0) * (Znth i ys_spec_2 0) ) + ((Znth j xs_spec_2 0) * (Znth j ys_spec_2 0) ) ) ) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i xs_spec_2 0) * (Znth i ys_spec_2 0) ) + ((Znth j xs_spec_2 0) * (Znth j ys_spec_2 0) ) ) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec_2 0) (Znth i ys_spec_2 0) (Znth j xs_spec_2 0) (Znth j ys_spec_2 0) a_pre b_pre )) (PreH4 : (rj = 0)) (PreH5 : (rj = 0)) (PreH6 : (ri = 0)) (PreH7 : (ri = 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  TT && emp 
|--
  “ (BestBefore paper seals i j 0 (0 + 1 ) (((Znth i xs_spec_2 0) * (Znth i ys_spec_2 0) ) + ((Znth j xs_spec_2 0) * (Znth j ys_spec_2 0) ) ) ) ” 
  &&  “ ((((Znth i xs_spec_2 0) * (Znth i ys_spec_2 0) ) + ((Znth j xs_spec_2 0) * (Znth j ys_spec_2 0) ) ) <= 20000) ”
  &&  emp
).

Definition solver_entail_wit_10_4_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i xs_spec_2 0) * (Znth i ys_spec_2 0) ) + ((Znth j xs_spec_2 0) * (Znth j ys_spec_2 0) ) ) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec_2 0) (Znth i ys_spec_2 0) (Znth j xs_spec_2 0) (Znth j ys_spec_2 0) a_pre b_pre )) (PreH4 : (rj = 0)) (PreH5 : (rj = 0)) (PreH6 : (ri = 0)) (PreH7 : (ri = 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  (BestBefore paper seals i j 0 (0 + 1 ) (((Znth i xs_spec_2 0) * (Znth i ys_spec_2 0) ) + ((Znth j xs_spec_2 0) * (Znth j ys_spec_2 0) ) ) )
.

Definition solver_entail_wit_10_4_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i xs_spec_2 0) * (Znth i ys_spec_2 0) ) + ((Znth j xs_spec_2 0) * (Znth j ys_spec_2 0) ) ) > best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec_2 0) (Znth i ys_spec_2 0) (Znth j xs_spec_2 0) (Znth j ys_spec_2 0) a_pre b_pre )) (PreH4 : (rj = 0)) (PreH5 : (rj = 0)) (PreH6 : (ri = 0)) (PreH7 : (ri = 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  ((((Znth i xs_spec_2 0) * (Znth i ys_spec_2 0) ) + ((Znth j xs_spec_2 0) * (Znth j ys_spec_2 0) ) ) <= 20000)
.

Definition solver_entail_wit_10_5 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i ys_spec_2 0) * (Znth i xs_spec_2 0) ) + ((Znth j ys_spec_2 0) * (Znth j xs_spec_2 0) ) ) <= best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec_2 0) (Znth i xs_spec_2 0) (Znth j ys_spec_2 0) (Znth j xs_spec_2 0) a_pre b_pre )) (PreH4 : (rj <> 0)) (PreH5 : (rj <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (ri <> 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  (IntArray.full x_pre n_pre xs_spec_2 )
  **  (IntArray.full y_pre n_pre ys_spec_2 )
|--
  EX (ys_spec: (@list Z))  (xs_spec: (@list Z)) ,
  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= (rj + 1 )) ” 
  &&  “ ((rj + 1 ) <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri (rj + 1 ) best ) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i ys_spec_2 0) * (Znth i xs_spec_2 0) ) + ((Znth j ys_spec_2 0) * (Znth j xs_spec_2 0) ) ) <= best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec_2 0) (Znth i xs_spec_2 0) (Znth j ys_spec_2 0) (Znth j xs_spec_2 0) a_pre b_pre )) (PreH4 : (rj <> 0)) (PreH5 : (rj <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (ri <> 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  TT && emp 
|--
  “ (BestBefore paper seals i j ri (rj + 1 ) best ) ”
  &&  emp
).

Definition solver_entail_wit_10_5_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i ys_spec_2 0) * (Znth i xs_spec_2 0) ) + ((Znth j ys_spec_2 0) * (Znth j xs_spec_2 0) ) ) <= best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec_2 0) (Znth i xs_spec_2 0) (Znth j ys_spec_2 0) (Znth j xs_spec_2 0) a_pre b_pre )) (PreH4 : (rj <> 0)) (PreH5 : (rj <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (ri <> 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  (BestBefore paper seals i j ri (rj + 1 ) best )
.

Definition solver_entail_wit_10_6 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i ys_spec_2 0) * (Znth i xs_spec_2 0) ) + ((Znth j xs_spec_2 0) * (Znth j ys_spec_2 0) ) ) <= best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec_2 0) (Znth i xs_spec_2 0) (Znth j xs_spec_2 0) (Znth j ys_spec_2 0) a_pre b_pre )) (PreH4 : (rj = 0)) (PreH5 : (rj = 0)) (PreH6 : (ri <> 0)) (PreH7 : (ri <> 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  (IntArray.full y_pre n_pre ys_spec_2 )
  **  (IntArray.full x_pre n_pre xs_spec_2 )
|--
  EX (ys_spec: (@list Z))  (xs_spec: (@list Z)) ,
  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= (rj + 1 )) ” 
  &&  “ ((rj + 1 ) <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri (rj + 1 ) best ) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i ys_spec_2 0) * (Znth i xs_spec_2 0) ) + ((Znth j xs_spec_2 0) * (Znth j ys_spec_2 0) ) ) <= best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec_2 0) (Znth i xs_spec_2 0) (Znth j xs_spec_2 0) (Znth j ys_spec_2 0) a_pre b_pre )) (PreH4 : (rj = 0)) (PreH5 : (rj = 0)) (PreH6 : (ri <> 0)) (PreH7 : (ri <> 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  TT && emp 
|--
  “ (BestBefore paper seals i j ri (0 + 1 ) best ) ”
  &&  emp
).

Definition solver_entail_wit_10_6_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i ys_spec_2 0) * (Znth i xs_spec_2 0) ) + ((Znth j xs_spec_2 0) * (Znth j ys_spec_2 0) ) ) <= best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i ys_spec_2 0) (Znth i xs_spec_2 0) (Znth j xs_spec_2 0) (Znth j ys_spec_2 0) a_pre b_pre )) (PreH4 : (rj = 0)) (PreH5 : (rj = 0)) (PreH6 : (ri <> 0)) (PreH7 : (ri <> 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  (BestBefore paper seals i j ri (0 + 1 ) best )
.

Definition solver_entail_wit_10_7 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i xs_spec_2 0) * (Znth i ys_spec_2 0) ) + ((Znth j ys_spec_2 0) * (Znth j xs_spec_2 0) ) ) <= best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec_2 0) (Znth i ys_spec_2 0) (Znth j ys_spec_2 0) (Znth j xs_spec_2 0) a_pre b_pre )) (PreH4 : (rj <> 0)) (PreH5 : (rj <> 0)) (PreH6 : (ri = 0)) (PreH7 : (ri = 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  (IntArray.full x_pre n_pre xs_spec_2 )
  **  (IntArray.full y_pre n_pre ys_spec_2 )
|--
  EX (ys_spec: (@list Z))  (xs_spec: (@list Z)) ,
  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= (rj + 1 )) ” 
  &&  “ ((rj + 1 ) <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri (rj + 1 ) best ) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i xs_spec_2 0) * (Znth i ys_spec_2 0) ) + ((Znth j ys_spec_2 0) * (Znth j xs_spec_2 0) ) ) <= best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec_2 0) (Znth i ys_spec_2 0) (Znth j ys_spec_2 0) (Znth j xs_spec_2 0) a_pre b_pre )) (PreH4 : (rj <> 0)) (PreH5 : (rj <> 0)) (PreH6 : (ri = 0)) (PreH7 : (ri = 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  TT && emp 
|--
  “ (BestBefore paper seals i j 0 (rj + 1 ) best ) ”
  &&  emp
).

Definition solver_entail_wit_10_7_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i xs_spec_2 0) * (Znth i ys_spec_2 0) ) + ((Znth j ys_spec_2 0) * (Znth j xs_spec_2 0) ) ) <= best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec_2 0) (Znth i ys_spec_2 0) (Znth j ys_spec_2 0) (Znth j xs_spec_2 0) a_pre b_pre )) (PreH4 : (rj <> 0)) (PreH5 : (rj <> 0)) (PreH6 : (ri = 0)) (PreH7 : (ri = 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  (BestBefore paper seals i j 0 (rj + 1 ) best )
.

Definition solver_entail_wit_10_8 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i xs_spec_2 0) * (Znth i ys_spec_2 0) ) + ((Znth j xs_spec_2 0) * (Znth j ys_spec_2 0) ) ) <= best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec_2 0) (Znth i ys_spec_2 0) (Znth j xs_spec_2 0) (Znth j ys_spec_2 0) a_pre b_pre )) (PreH4 : (rj = 0)) (PreH5 : (rj = 0)) (PreH6 : (ri = 0)) (PreH7 : (ri = 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  (IntArray.full y_pre n_pre ys_spec_2 )
  **  (IntArray.full x_pre n_pre xs_spec_2 )
|--
  EX (ys_spec: (@list Z))  (xs_spec: (@list Z)) ,
  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= (rj + 1 )) ” 
  &&  “ ((rj + 1 ) <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri (rj + 1 ) best ) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i xs_spec_2 0) * (Znth i ys_spec_2 0) ) + ((Znth j xs_spec_2 0) * (Znth j ys_spec_2 0) ) ) <= best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec_2 0) (Znth i ys_spec_2 0) (Znth j xs_spec_2 0) (Znth j ys_spec_2 0) a_pre b_pre )) (PreH4 : (rj = 0)) (PreH5 : (rj = 0)) (PreH6 : (ri = 0)) (PreH7 : (ri = 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  TT && emp 
|--
  “ (BestBefore paper seals i j 0 (0 + 1 ) best ) ”
  &&  emp
).

Definition solver_entail_wit_10_8_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((((Znth i xs_spec_2 0) * (Znth i ys_spec_2 0) ) + ((Znth j xs_spec_2 0) * (Znth j ys_spec_2 0) ) ) <= best)) (PreH2 : (retval = 1)) (PreH3 : (FitsDims (Znth i xs_spec_2 0) (Znth i ys_spec_2 0) (Znth j xs_spec_2 0) (Znth j ys_spec_2 0) a_pre b_pre )) (PreH4 : (rj = 0)) (PreH5 : (rj = 0)) (PreH6 : (ri = 0)) (PreH7 : (ri = 0)) (PreH8 : (rj < 2)) (PreH9 : (1 <= (fst (paper)))) (PreH10 : ((fst (paper)) <= 100)) (PreH11 : (1 <= (snd (paper)))) (PreH12 : ((snd (paper)) <= 100)) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100)) (PreH15 : ((fst (paper)) = a_pre)) (PreH16 : ((snd (paper)) = b_pre)) (PreH17 : (n_pre = (Zlength (seals)))) (PreH18 : ((Zlength (xs_spec_2)) = n_pre)) (PreH19 : ((Zlength (ys_spec_2)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH21 : (0 <= i)) (PreH22 : (i < j)) (PreH23 : (j < n_pre)) (PreH24 : (0 <= ri)) (PreH25 : (ri < 2)) (PreH26 : (0 <= rj)) (PreH27 : (rj <= 2)) (PreH28 : (0 <= best)) (PreH29 : (best <= 20000)) (PreH30 : (BestBefore paper seals i j ri rj best )) (PreH31 : (retval <> 0)) ,
  (BestBefore paper seals i j 0 (0 + 1 ) best )
.

Definition solver_entail_wit_10_9 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 0)) (PreH2 : ~((FitsDims (Znth i ys_spec_2 0) (Znth i xs_spec_2 0) (Znth j ys_spec_2 0) (Znth j xs_spec_2 0) a_pre b_pre ))) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec_2)) = n_pre)) (PreH18 : ((Zlength (ys_spec_2)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval = 0)) ,
  (IntArray.full x_pre n_pre xs_spec_2 )
  **  (IntArray.full y_pre n_pre ys_spec_2 )
|--
  EX (ys_spec: (@list Z))  (xs_spec: (@list Z)) ,
  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= (rj + 1 )) ” 
  &&  “ ((rj + 1 ) <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri (rj + 1 ) best ) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 0)) (PreH2 : ~((FitsDims (Znth i ys_spec_2 0) (Znth i xs_spec_2 0) (Znth j ys_spec_2 0) (Znth j xs_spec_2 0) a_pre b_pre ))) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec_2)) = n_pre)) (PreH18 : ((Zlength (ys_spec_2)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval = 0)) ,
  TT && emp 
|--
  “ (BestBefore paper seals i j ri (rj + 1 ) best ) ”
  &&  emp
).

Definition solver_entail_wit_10_9_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 0)) (PreH2 : ~((FitsDims (Znth i ys_spec_2 0) (Znth i xs_spec_2 0) (Znth j ys_spec_2 0) (Znth j xs_spec_2 0) a_pre b_pre ))) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec_2)) = n_pre)) (PreH18 : ((Zlength (ys_spec_2)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval = 0)) ,
  (BestBefore paper seals i j ri (rj + 1 ) best )
.

Definition solver_entail_wit_10_10 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 0)) (PreH2 : ~((FitsDims (Znth i ys_spec_2 0) (Znth i xs_spec_2 0) (Znth j xs_spec_2 0) (Znth j ys_spec_2 0) a_pre b_pre ))) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec_2)) = n_pre)) (PreH18 : ((Zlength (ys_spec_2)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval = 0)) ,
  (IntArray.full y_pre n_pre ys_spec_2 )
  **  (IntArray.full x_pre n_pre xs_spec_2 )
|--
  EX (ys_spec: (@list Z))  (xs_spec: (@list Z)) ,
  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= (rj + 1 )) ” 
  &&  “ ((rj + 1 ) <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri (rj + 1 ) best ) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 0)) (PreH2 : ~((FitsDims (Znth i ys_spec_2 0) (Znth i xs_spec_2 0) (Znth j xs_spec_2 0) (Znth j ys_spec_2 0) a_pre b_pre ))) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec_2)) = n_pre)) (PreH18 : ((Zlength (ys_spec_2)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval = 0)) ,
  TT && emp 
|--
  “ (BestBefore paper seals i j ri (0 + 1 ) best ) ”
  &&  emp
).

Definition solver_entail_wit_10_10_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 0)) (PreH2 : ~((FitsDims (Znth i ys_spec_2 0) (Znth i xs_spec_2 0) (Znth j xs_spec_2 0) (Znth j ys_spec_2 0) a_pre b_pre ))) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri <> 0)) (PreH6 : (ri <> 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec_2)) = n_pre)) (PreH18 : ((Zlength (ys_spec_2)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval = 0)) ,
  (BestBefore paper seals i j ri (0 + 1 ) best )
.

Definition solver_entail_wit_10_11 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 0)) (PreH2 : ~((FitsDims (Znth i xs_spec_2 0) (Znth i ys_spec_2 0) (Znth j ys_spec_2 0) (Znth j xs_spec_2 0) a_pre b_pre ))) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec_2)) = n_pre)) (PreH18 : ((Zlength (ys_spec_2)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval = 0)) ,
  (IntArray.full x_pre n_pre xs_spec_2 )
  **  (IntArray.full y_pre n_pre ys_spec_2 )
|--
  EX (ys_spec: (@list Z))  (xs_spec: (@list Z)) ,
  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= (rj + 1 )) ” 
  &&  “ ((rj + 1 ) <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri (rj + 1 ) best ) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 0)) (PreH2 : ~((FitsDims (Znth i xs_spec_2 0) (Znth i ys_spec_2 0) (Znth j ys_spec_2 0) (Znth j xs_spec_2 0) a_pre b_pre ))) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec_2)) = n_pre)) (PreH18 : ((Zlength (ys_spec_2)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval = 0)) ,
  TT && emp 
|--
  “ (BestBefore paper seals i j 0 (rj + 1 ) best ) ”
  &&  emp
).

Definition solver_entail_wit_10_11_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 0)) (PreH2 : ~((FitsDims (Znth i xs_spec_2 0) (Znth i ys_spec_2 0) (Znth j ys_spec_2 0) (Znth j xs_spec_2 0) a_pre b_pre ))) (PreH3 : (rj <> 0)) (PreH4 : (rj <> 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec_2)) = n_pre)) (PreH18 : ((Zlength (ys_spec_2)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval = 0)) ,
  (BestBefore paper seals i j 0 (rj + 1 ) best )
.

Definition solver_entail_wit_10_12 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 0)) (PreH2 : ~((FitsDims (Znth i xs_spec_2 0) (Znth i ys_spec_2 0) (Znth j xs_spec_2 0) (Znth j ys_spec_2 0) a_pre b_pre ))) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec_2)) = n_pre)) (PreH18 : ((Zlength (ys_spec_2)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval = 0)) ,
  (IntArray.full y_pre n_pre ys_spec_2 )
  **  (IntArray.full x_pre n_pre xs_spec_2 )
|--
  EX (ys_spec: (@list Z))  (xs_spec: (@list Z)) ,
  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= (rj + 1 )) ” 
  &&  “ ((rj + 1 ) <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri (rj + 1 ) best ) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 0)) (PreH2 : ~((FitsDims (Znth i xs_spec_2 0) (Znth i ys_spec_2 0) (Znth j xs_spec_2 0) (Znth j ys_spec_2 0) a_pre b_pre ))) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec_2)) = n_pre)) (PreH18 : ((Zlength (ys_spec_2)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval = 0)) ,
  TT && emp 
|--
  “ (BestBefore paper seals i j 0 (0 + 1 ) best ) ”
  &&  emp
).

Definition solver_entail_wit_10_12_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = 0)) (PreH2 : ~((FitsDims (Znth i xs_spec_2 0) (Znth i ys_spec_2 0) (Znth j xs_spec_2 0) (Znth j ys_spec_2 0) a_pre b_pre ))) (PreH3 : (rj = 0)) (PreH4 : (rj = 0)) (PreH5 : (ri = 0)) (PreH6 : (ri = 0)) (PreH7 : (rj < 2)) (PreH8 : (1 <= (fst (paper)))) (PreH9 : ((fst (paper)) <= 100)) (PreH10 : (1 <= (snd (paper)))) (PreH11 : ((snd (paper)) <= 100)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100)) (PreH14 : ((fst (paper)) = a_pre)) (PreH15 : ((snd (paper)) = b_pre)) (PreH16 : (n_pre = (Zlength (seals)))) (PreH17 : ((Zlength (xs_spec_2)) = n_pre)) (PreH18 : ((Zlength (ys_spec_2)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH20 : (0 <= i)) (PreH21 : (i < j)) (PreH22 : (j < n_pre)) (PreH23 : (0 <= ri)) (PreH24 : (ri < 2)) (PreH25 : (0 <= rj)) (PreH26 : (rj <= 2)) (PreH27 : (0 <= best)) (PreH28 : (best <= 20000)) (PreH29 : (BestBefore paper seals i j ri rj best )) (PreH30 : (retval = 0)) ,
  (BestBefore paper seals i j 0 (0 + 1 ) best )
.

Definition solver_return_wit_1 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (i_2: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z))  __default__Prod_Z_Z (PreH1 : (i_2 >= n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH14 : (0 <= i_2)) (PreH15 : (i_2 <= n_pre)) (PreH16 : (0 <= best)) (PreH17 : (best <= 20000)) (PreH18 : (BestBefore paper seals i_2 (i_2 + 1 ) 0 0 best )) ,
  (IntArray.full x_pre n_pre xs_spec_2 )
  **  (IntArray.full y_pre n_pre ys_spec_2 )
|--
  EX (ys_spec: (@list Z))  (xs_spec: (@list Z)) ,
  “ (Spec paper seals best ) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i xs_spec 0) = (fst ((Znth i seals __default__Prod_Z_Z)))) /\ ((Znth i ys_spec 0) = (snd ((Znth i seals __default__Prod_Z_Z)))))) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (i_2: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z))  __default__Prod_Z_Z (PreH1 : (i_2 >= n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH14 : (0 <= i_2)) (PreH15 : (i_2 <= n_pre)) (PreH16 : (0 <= best)) (PreH17 : (best <= 20000)) (PreH18 : (BestBefore paper seals i_2 (i_2 + 1 ) 0 0 best )) ,
  TT && emp 
|--
  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i xs_spec_2 0) = (fst ((Znth i seals __default__Prod_Z_Z)))) /\ ((Znth i ys_spec_2 0) = (snd ((Znth i seals __default__Prod_Z_Z)))))) ” 
  &&  “ (Spec paper seals best ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (i_2: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z))  __default__Prod_Z_Z (PreH1 : (i_2 >= n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH14 : (0 <= i_2)) (PreH15 : (i_2 <= n_pre)) (PreH16 : (0 <= best)) (PreH17 : (best <= 20000)) (PreH18 : (BestBefore paper seals i_2 (i_2 + 1 ) 0 0 best )) ,
  forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i xs_spec_2 0) = (fst ((Znth i seals __default__Prod_Z_Z)))) /\ ((Znth i ys_spec_2 0) = (snd ((Znth i seals __default__Prod_Z_Z))))))
.

Definition solver_return_wit_1_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (i_2: Z) (ys_spec_2: (@list Z)) (xs_spec_2: (@list Z))  __default__Prod_Z_Z (PreH1 : (i_2 >= n_pre)) (PreH2 : (1 <= (fst (paper)))) (PreH3 : ((fst (paper)) <= 100)) (PreH4 : (1 <= (snd (paper)))) (PreH5 : ((snd (paper)) <= 100)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : ((fst (paper)) = a_pre)) (PreH9 : ((snd (paper)) = b_pre)) (PreH10 : (n_pre = (Zlength (seals)))) (PreH11 : ((Zlength (xs_spec_2)) = n_pre)) (PreH12 : ((Zlength (ys_spec_2)) = n_pre)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec_2 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec_2 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH14 : (0 <= i_2)) (PreH15 : (i_2 <= n_pre)) (PreH16 : (0 <= best)) (PreH17 : (best <= 20000)) (PreH18 : (BestBefore paper seals i_2 (i_2 + 1 ) 0 0 best )) ,
  (Spec paper seals best )
.

Definition solver_partial_solve_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (ri <> 0)) (PreH2 : (ri <> 0)) (PreH3 : (rj < 2)) (PreH4 : (1 <= (fst (paper)))) (PreH5 : ((fst (paper)) <= 100)) (PreH6 : (1 <= (snd (paper)))) (PreH7 : ((snd (paper)) <= 100)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((fst (paper)) = a_pre)) (PreH11 : ((snd (paper)) = b_pre)) (PreH12 : (n_pre = (Zlength (seals)))) (PreH13 : ((Zlength (xs_spec)) = n_pre)) (PreH14 : ((Zlength (ys_spec)) = n_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH16 : (0 <= i)) (PreH17 : (i < j)) (PreH18 : (j < n_pre)) (PreH19 : (0 <= ri)) (PreH20 : (ri < 2)) (PreH21 : (0 <= rj)) (PreH22 : (rj <= 2)) (PreH23 : (0 <= best)) (PreH24 : (best <= 20000)) (PreH25 : (BestBefore paper seals i j ri rj best )) ,
  (IntArray.full y_pre n_pre ys_spec )
  **  (IntArray.full x_pre n_pre xs_spec )
|--
  “ (ri <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ”
  &&  (((x_pre + (i * sizeof(INT)))) # Int  |-> (Znth i xs_spec 0))
  **  (IntArray.missing_i x_pre i 0 n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
.

Definition solver_partial_solve_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (ri = 0)) (PreH2 : (ri = 0)) (PreH3 : (rj < 2)) (PreH4 : (1 <= (fst (paper)))) (PreH5 : ((fst (paper)) <= 100)) (PreH6 : (1 <= (snd (paper)))) (PreH7 : ((snd (paper)) <= 100)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : ((fst (paper)) = a_pre)) (PreH11 : ((snd (paper)) = b_pre)) (PreH12 : (n_pre = (Zlength (seals)))) (PreH13 : ((Zlength (xs_spec)) = n_pre)) (PreH14 : ((Zlength (ys_spec)) = n_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH16 : (0 <= i)) (PreH17 : (i < j)) (PreH18 : (j < n_pre)) (PreH19 : (0 <= ri)) (PreH20 : (ri < 2)) (PreH21 : (0 <= rj)) (PreH22 : (rj <= 2)) (PreH23 : (0 <= best)) (PreH24 : (best <= 20000)) (PreH25 : (BestBefore paper seals i j ri rj best )) ,
  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
|--
  “ (ri = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ”
  &&  (((y_pre + (i * sizeof(INT)))) # Int  |-> (Znth i ys_spec 0))
  **  (IntArray.missing_i y_pre i 0 n_pre ys_spec )
  **  (IntArray.full x_pre n_pre xs_spec )
.

Definition solver_partial_solve_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (ri <> 0)) (PreH2 : (rj < 2)) (PreH3 : (1 <= (fst (paper)))) (PreH4 : ((fst (paper)) <= 100)) (PreH5 : (1 <= (snd (paper)))) (PreH6 : ((snd (paper)) <= 100)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : ((fst (paper)) = a_pre)) (PreH10 : ((snd (paper)) = b_pre)) (PreH11 : (n_pre = (Zlength (seals)))) (PreH12 : ((Zlength (xs_spec)) = n_pre)) (PreH13 : ((Zlength (ys_spec)) = n_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH15 : (0 <= i)) (PreH16 : (i < j)) (PreH17 : (j < n_pre)) (PreH18 : (0 <= ri)) (PreH19 : (ri < 2)) (PreH20 : (0 <= rj)) (PreH21 : (rj <= 2)) (PreH22 : (0 <= best)) (PreH23 : (best <= 20000)) (PreH24 : (BestBefore paper seals i j ri rj best )) ,
  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
|--
  “ (ri <> 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ”
  &&  (((y_pre + (i * sizeof(INT)))) # Int  |-> (Znth i ys_spec 0))
  **  (IntArray.missing_i y_pre i 0 n_pre ys_spec )
  **  (IntArray.full x_pre n_pre xs_spec )
.

Definition solver_partial_solve_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (ri = 0)) (PreH2 : (rj < 2)) (PreH3 : (1 <= (fst (paper)))) (PreH4 : ((fst (paper)) <= 100)) (PreH5 : (1 <= (snd (paper)))) (PreH6 : ((snd (paper)) <= 100)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : ((fst (paper)) = a_pre)) (PreH10 : ((snd (paper)) = b_pre)) (PreH11 : (n_pre = (Zlength (seals)))) (PreH12 : ((Zlength (xs_spec)) = n_pre)) (PreH13 : ((Zlength (ys_spec)) = n_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH15 : (0 <= i)) (PreH16 : (i < j)) (PreH17 : (j < n_pre)) (PreH18 : (0 <= ri)) (PreH19 : (ri < 2)) (PreH20 : (0 <= rj)) (PreH21 : (rj <= 2)) (PreH22 : (0 <= best)) (PreH23 : (best <= 20000)) (PreH24 : (BestBefore paper seals i j ri rj best )) ,
  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
|--
  “ (ri = 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ”
  &&  (((x_pre + (i * sizeof(INT)))) # Int  |-> (Znth i xs_spec 0))
  **  (IntArray.missing_i x_pre i 0 n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
.

Definition solver_partial_solve_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (rj <> 0)) (PreH2 : (rj <> 0)) (PreH3 : (ri <> 0)) (PreH4 : (ri <> 0)) (PreH5 : (rj < 2)) (PreH6 : (1 <= (fst (paper)))) (PreH7 : ((fst (paper)) <= 100)) (PreH8 : (1 <= (snd (paper)))) (PreH9 : ((snd (paper)) <= 100)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : ((fst (paper)) = a_pre)) (PreH13 : ((snd (paper)) = b_pre)) (PreH14 : (n_pre = (Zlength (seals)))) (PreH15 : ((Zlength (xs_spec)) = n_pre)) (PreH16 : ((Zlength (ys_spec)) = n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH18 : (0 <= i)) (PreH19 : (i < j)) (PreH20 : (j < n_pre)) (PreH21 : (0 <= ri)) (PreH22 : (ri < 2)) (PreH23 : (0 <= rj)) (PreH24 : (rj <= 2)) (PreH25 : (0 <= best)) (PreH26 : (best <= 20000)) (PreH27 : (BestBefore paper seals i j ri rj best )) ,
  (IntArray.full y_pre n_pre ys_spec )
  **  (IntArray.full x_pre n_pre xs_spec )
|--
  “ (rj <> 0) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ”
  &&  (((x_pre + (j * sizeof(INT)))) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.missing_i x_pre j 0 n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
.

Definition solver_partial_solve_wit_6 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (rj = 0)) (PreH2 : (rj = 0)) (PreH3 : (ri <> 0)) (PreH4 : (ri <> 0)) (PreH5 : (rj < 2)) (PreH6 : (1 <= (fst (paper)))) (PreH7 : ((fst (paper)) <= 100)) (PreH8 : (1 <= (snd (paper)))) (PreH9 : ((snd (paper)) <= 100)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : ((fst (paper)) = a_pre)) (PreH13 : ((snd (paper)) = b_pre)) (PreH14 : (n_pre = (Zlength (seals)))) (PreH15 : ((Zlength (xs_spec)) = n_pre)) (PreH16 : ((Zlength (ys_spec)) = n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH18 : (0 <= i)) (PreH19 : (i < j)) (PreH20 : (j < n_pre)) (PreH21 : (0 <= ri)) (PreH22 : (ri < 2)) (PreH23 : (0 <= rj)) (PreH24 : (rj <= 2)) (PreH25 : (0 <= best)) (PreH26 : (best <= 20000)) (PreH27 : (BestBefore paper seals i j ri rj best )) ,
  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
|--
  “ (rj = 0) ” 
  &&  “ (rj = 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ”
  &&  (((y_pre + (j * sizeof(INT)))) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.missing_i y_pre j 0 n_pre ys_spec )
  **  (IntArray.full x_pre n_pre xs_spec )
.

Definition solver_partial_solve_wit_7 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (rj <> 0)) (PreH2 : (rj <> 0)) (PreH3 : (ri = 0)) (PreH4 : (ri = 0)) (PreH5 : (rj < 2)) (PreH6 : (1 <= (fst (paper)))) (PreH7 : ((fst (paper)) <= 100)) (PreH8 : (1 <= (snd (paper)))) (PreH9 : ((snd (paper)) <= 100)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : ((fst (paper)) = a_pre)) (PreH13 : ((snd (paper)) = b_pre)) (PreH14 : (n_pre = (Zlength (seals)))) (PreH15 : ((Zlength (xs_spec)) = n_pre)) (PreH16 : ((Zlength (ys_spec)) = n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH18 : (0 <= i)) (PreH19 : (i < j)) (PreH20 : (j < n_pre)) (PreH21 : (0 <= ri)) (PreH22 : (ri < 2)) (PreH23 : (0 <= rj)) (PreH24 : (rj <= 2)) (PreH25 : (0 <= best)) (PreH26 : (best <= 20000)) (PreH27 : (BestBefore paper seals i j ri rj best )) ,
  (IntArray.full y_pre n_pre ys_spec )
  **  (IntArray.full x_pre n_pre xs_spec )
|--
  “ (rj <> 0) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ”
  &&  (((x_pre + (j * sizeof(INT)))) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.missing_i x_pre j 0 n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
.

Definition solver_partial_solve_wit_8 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (rj = 0)) (PreH2 : (rj = 0)) (PreH3 : (ri = 0)) (PreH4 : (ri = 0)) (PreH5 : (rj < 2)) (PreH6 : (1 <= (fst (paper)))) (PreH7 : ((fst (paper)) <= 100)) (PreH8 : (1 <= (snd (paper)))) (PreH9 : ((snd (paper)) <= 100)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : ((fst (paper)) = a_pre)) (PreH13 : ((snd (paper)) = b_pre)) (PreH14 : (n_pre = (Zlength (seals)))) (PreH15 : ((Zlength (xs_spec)) = n_pre)) (PreH16 : ((Zlength (ys_spec)) = n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH18 : (0 <= i)) (PreH19 : (i < j)) (PreH20 : (j < n_pre)) (PreH21 : (0 <= ri)) (PreH22 : (ri < 2)) (PreH23 : (0 <= rj)) (PreH24 : (rj <= 2)) (PreH25 : (0 <= best)) (PreH26 : (best <= 20000)) (PreH27 : (BestBefore paper seals i j ri rj best )) ,
  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
|--
  “ (rj = 0) ” 
  &&  “ (rj = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ”
  &&  (((y_pre + (j * sizeof(INT)))) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.missing_i y_pre j 0 n_pre ys_spec )
  **  (IntArray.full x_pre n_pre xs_spec )
.

Definition solver_partial_solve_wit_9 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (rj <> 0)) (PreH2 : (ri <> 0)) (PreH3 : (ri <> 0)) (PreH4 : (rj < 2)) (PreH5 : (1 <= (fst (paper)))) (PreH6 : ((fst (paper)) <= 100)) (PreH7 : (1 <= (snd (paper)))) (PreH8 : ((snd (paper)) <= 100)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : ((fst (paper)) = a_pre)) (PreH12 : ((snd (paper)) = b_pre)) (PreH13 : (n_pre = (Zlength (seals)))) (PreH14 : ((Zlength (xs_spec)) = n_pre)) (PreH15 : ((Zlength (ys_spec)) = n_pre)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH17 : (0 <= i)) (PreH18 : (i < j)) (PreH19 : (j < n_pre)) (PreH20 : (0 <= ri)) (PreH21 : (ri < 2)) (PreH22 : (0 <= rj)) (PreH23 : (rj <= 2)) (PreH24 : (0 <= best)) (PreH25 : (best <= 20000)) (PreH26 : (BestBefore paper seals i j ri rj best )) ,
  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
|--
  “ (rj <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ”
  &&  (((y_pre + (j * sizeof(INT)))) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.missing_i y_pre j 0 n_pre ys_spec )
  **  (IntArray.full x_pre n_pre xs_spec )
.

Definition solver_partial_solve_wit_10 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (rj = 0)) (PreH2 : (ri <> 0)) (PreH3 : (ri <> 0)) (PreH4 : (rj < 2)) (PreH5 : (1 <= (fst (paper)))) (PreH6 : ((fst (paper)) <= 100)) (PreH7 : (1 <= (snd (paper)))) (PreH8 : ((snd (paper)) <= 100)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : ((fst (paper)) = a_pre)) (PreH12 : ((snd (paper)) = b_pre)) (PreH13 : (n_pre = (Zlength (seals)))) (PreH14 : ((Zlength (xs_spec)) = n_pre)) (PreH15 : ((Zlength (ys_spec)) = n_pre)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH17 : (0 <= i)) (PreH18 : (i < j)) (PreH19 : (j < n_pre)) (PreH20 : (0 <= ri)) (PreH21 : (ri < 2)) (PreH22 : (0 <= rj)) (PreH23 : (rj <= 2)) (PreH24 : (0 <= best)) (PreH25 : (best <= 20000)) (PreH26 : (BestBefore paper seals i j ri rj best )) ,
  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
|--
  “ (rj = 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ”
  &&  (((x_pre + (j * sizeof(INT)))) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.missing_i x_pre j 0 n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
.

Definition solver_partial_solve_wit_11 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (rj <> 0)) (PreH2 : (ri = 0)) (PreH3 : (ri = 0)) (PreH4 : (rj < 2)) (PreH5 : (1 <= (fst (paper)))) (PreH6 : ((fst (paper)) <= 100)) (PreH7 : (1 <= (snd (paper)))) (PreH8 : ((snd (paper)) <= 100)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : ((fst (paper)) = a_pre)) (PreH12 : ((snd (paper)) = b_pre)) (PreH13 : (n_pre = (Zlength (seals)))) (PreH14 : ((Zlength (xs_spec)) = n_pre)) (PreH15 : ((Zlength (ys_spec)) = n_pre)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH17 : (0 <= i)) (PreH18 : (i < j)) (PreH19 : (j < n_pre)) (PreH20 : (0 <= ri)) (PreH21 : (ri < 2)) (PreH22 : (0 <= rj)) (PreH23 : (rj <= 2)) (PreH24 : (0 <= best)) (PreH25 : (best <= 20000)) (PreH26 : (BestBefore paper seals i j ri rj best )) ,
  (IntArray.full y_pre n_pre ys_spec )
  **  (IntArray.full x_pre n_pre xs_spec )
|--
  “ (rj <> 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ”
  &&  (((y_pre + (j * sizeof(INT)))) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.missing_i y_pre j 0 n_pre ys_spec )
  **  (IntArray.full x_pre n_pre xs_spec )
.

Definition solver_partial_solve_wit_12 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (rj = 0)) (PreH2 : (ri = 0)) (PreH3 : (ri = 0)) (PreH4 : (rj < 2)) (PreH5 : (1 <= (fst (paper)))) (PreH6 : ((fst (paper)) <= 100)) (PreH7 : (1 <= (snd (paper)))) (PreH8 : ((snd (paper)) <= 100)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : ((fst (paper)) = a_pre)) (PreH12 : ((snd (paper)) = b_pre)) (PreH13 : (n_pre = (Zlength (seals)))) (PreH14 : ((Zlength (xs_spec)) = n_pre)) (PreH15 : ((Zlength (ys_spec)) = n_pre)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH17 : (0 <= i)) (PreH18 : (i < j)) (PreH19 : (j < n_pre)) (PreH20 : (0 <= ri)) (PreH21 : (ri < 2)) (PreH22 : (0 <= rj)) (PreH23 : (rj <= 2)) (PreH24 : (0 <= best)) (PreH25 : (best <= 20000)) (PreH26 : (BestBefore paper seals i j ri rj best )) ,
  (IntArray.full y_pre n_pre ys_spec )
  **  (IntArray.full x_pre n_pre xs_spec )
|--
  “ (rj = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ”
  &&  (((x_pre + (j * sizeof(INT)))) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.missing_i x_pre j 0 n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
.

Definition solver_partial_solve_wit_13_pure := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (rj <> 0)) (PreH2 : (rj <> 0)) (PreH3 : (ri <> 0)) (PreH4 : (ri <> 0)) (PreH5 : (rj < 2)) (PreH6 : (1 <= (fst (paper)))) (PreH7 : ((fst (paper)) <= 100)) (PreH8 : (1 <= (snd (paper)))) (PreH9 : ((snd (paper)) <= 100)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : ((fst (paper)) = a_pre)) (PreH13 : ((snd (paper)) = b_pre)) (PreH14 : (n_pre = (Zlength (seals)))) (PreH15 : ((Zlength (xs_spec)) = n_pre)) (PreH16 : ((Zlength (ys_spec)) = n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH18 : (0 <= i)) (PreH19 : (i < j)) (PreH20 : (j < n_pre)) (PreH21 : (0 <= ri)) (PreH22 : (ri < 2)) (PreH23 : (0 <= rj)) (PreH24 : (rj <= 2)) (PreH25 : (0 <= best)) (PreH26 : (best <= 20000)) (PreH27 : (BestBefore paper seals i j ri rj best )) ,
  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (1 <= (Znth i ys_spec 0)) ” 
  &&  “ ((Znth i ys_spec 0) <= 100) ” 
  &&  “ (1 <= (Znth i xs_spec 0)) ” 
  &&  “ ((Znth i xs_spec 0) <= 100) ” 
  &&  “ (1 <= (Znth j ys_spec 0)) ” 
  &&  “ ((Znth j ys_spec 0) <= 100) ” 
  &&  “ (1 <= (Znth j xs_spec 0)) ” 
  &&  “ ((Znth j xs_spec 0) <= 100) ” 
  &&  “ (1 <= a_pre) ” 
  &&  “ (a_pre <= 100) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (b_pre <= 100) ”
.

Definition solver_partial_solve_wit_13_aux := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (rj <> 0)) (PreH2 : (rj <> 0)) (PreH3 : (ri <> 0)) (PreH4 : (ri <> 0)) (PreH5 : (rj < 2)) (PreH6 : (1 <= (fst (paper)))) (PreH7 : ((fst (paper)) <= 100)) (PreH8 : (1 <= (snd (paper)))) (PreH9 : ((snd (paper)) <= 100)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : ((fst (paper)) = a_pre)) (PreH13 : ((snd (paper)) = b_pre)) (PreH14 : (n_pre = (Zlength (seals)))) (PreH15 : ((Zlength (xs_spec)) = n_pre)) (PreH16 : ((Zlength (ys_spec)) = n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH18 : (0 <= i)) (PreH19 : (i < j)) (PreH20 : (j < n_pre)) (PreH21 : (0 <= ri)) (PreH22 : (ri < 2)) (PreH23 : (0 <= rj)) (PreH24 : (rj <= 2)) (PreH25 : (0 <= best)) (PreH26 : (best <= 20000)) (PreH27 : (BestBefore paper seals i j ri rj best )) ,
  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
|--
  “ (1 <= (Znth i ys_spec 0)) ” 
  &&  “ ((Znth i ys_spec 0) <= 100) ” 
  &&  “ (1 <= (Znth i xs_spec 0)) ” 
  &&  “ ((Znth i xs_spec 0) <= 100) ” 
  &&  “ (1 <= (Znth j ys_spec 0)) ” 
  &&  “ ((Znth j ys_spec 0) <= 100) ” 
  &&  “ (1 <= (Znth j xs_spec 0)) ” 
  &&  “ ((Znth j xs_spec 0) <= 100) ” 
  &&  “ (1 <= a_pre) ” 
  &&  “ (a_pre <= 100) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (b_pre <= 100) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
.

Definition solver_partial_solve_wit_13 := solver_partial_solve_wit_13_pure -> solver_partial_solve_wit_13_aux.

Definition solver_partial_solve_wit_14_pure := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (rj = 0)) (PreH2 : (rj = 0)) (PreH3 : (ri <> 0)) (PreH4 : (ri <> 0)) (PreH5 : (rj < 2)) (PreH6 : (1 <= (fst (paper)))) (PreH7 : ((fst (paper)) <= 100)) (PreH8 : (1 <= (snd (paper)))) (PreH9 : ((snd (paper)) <= 100)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : ((fst (paper)) = a_pre)) (PreH13 : ((snd (paper)) = b_pre)) (PreH14 : (n_pre = (Zlength (seals)))) (PreH15 : ((Zlength (xs_spec)) = n_pre)) (PreH16 : ((Zlength (ys_spec)) = n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH18 : (0 <= i)) (PreH19 : (i < j)) (PreH20 : (j < n_pre)) (PreH21 : (0 <= ri)) (PreH22 : (ri < 2)) (PreH23 : (0 <= rj)) (PreH24 : (rj <= 2)) (PreH25 : (0 <= best)) (PreH26 : (best <= 20000)) (PreH27 : (BestBefore paper seals i j ri rj best )) ,
  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (1 <= (Znth i ys_spec 0)) ” 
  &&  “ ((Znth i ys_spec 0) <= 100) ” 
  &&  “ (1 <= (Znth i xs_spec 0)) ” 
  &&  “ ((Znth i xs_spec 0) <= 100) ” 
  &&  “ (1 <= (Znth j xs_spec 0)) ” 
  &&  “ ((Znth j xs_spec 0) <= 100) ” 
  &&  “ (1 <= (Znth j ys_spec 0)) ” 
  &&  “ ((Znth j ys_spec 0) <= 100) ” 
  &&  “ (1 <= a_pre) ” 
  &&  “ (a_pre <= 100) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (b_pre <= 100) ”
.

Definition solver_partial_solve_wit_14_aux := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (rj = 0)) (PreH2 : (rj = 0)) (PreH3 : (ri <> 0)) (PreH4 : (ri <> 0)) (PreH5 : (rj < 2)) (PreH6 : (1 <= (fst (paper)))) (PreH7 : ((fst (paper)) <= 100)) (PreH8 : (1 <= (snd (paper)))) (PreH9 : ((snd (paper)) <= 100)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : ((fst (paper)) = a_pre)) (PreH13 : ((snd (paper)) = b_pre)) (PreH14 : (n_pre = (Zlength (seals)))) (PreH15 : ((Zlength (xs_spec)) = n_pre)) (PreH16 : ((Zlength (ys_spec)) = n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH18 : (0 <= i)) (PreH19 : (i < j)) (PreH20 : (j < n_pre)) (PreH21 : (0 <= ri)) (PreH22 : (ri < 2)) (PreH23 : (0 <= rj)) (PreH24 : (rj <= 2)) (PreH25 : (0 <= best)) (PreH26 : (best <= 20000)) (PreH27 : (BestBefore paper seals i j ri rj best )) ,
  (IntArray.full y_pre n_pre ys_spec )
  **  (IntArray.full x_pre n_pre xs_spec )
|--
  “ (1 <= (Znth i ys_spec 0)) ” 
  &&  “ ((Znth i ys_spec 0) <= 100) ” 
  &&  “ (1 <= (Znth i xs_spec 0)) ” 
  &&  “ ((Znth i xs_spec 0) <= 100) ” 
  &&  “ (1 <= (Znth j xs_spec 0)) ” 
  &&  “ ((Znth j xs_spec 0) <= 100) ” 
  &&  “ (1 <= (Znth j ys_spec 0)) ” 
  &&  “ ((Znth j ys_spec 0) <= 100) ” 
  &&  “ (1 <= a_pre) ” 
  &&  “ (a_pre <= 100) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (b_pre <= 100) ” 
  &&  “ (rj = 0) ” 
  &&  “ (rj = 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (ri <> 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ”
  &&  (IntArray.full y_pre n_pre ys_spec )
  **  (IntArray.full x_pre n_pre xs_spec )
.

Definition solver_partial_solve_wit_14 := solver_partial_solve_wit_14_pure -> solver_partial_solve_wit_14_aux.

Definition solver_partial_solve_wit_15_pure := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (rj <> 0)) (PreH2 : (rj <> 0)) (PreH3 : (ri = 0)) (PreH4 : (ri = 0)) (PreH5 : (rj < 2)) (PreH6 : (1 <= (fst (paper)))) (PreH7 : ((fst (paper)) <= 100)) (PreH8 : (1 <= (snd (paper)))) (PreH9 : ((snd (paper)) <= 100)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : ((fst (paper)) = a_pre)) (PreH13 : ((snd (paper)) = b_pre)) (PreH14 : (n_pre = (Zlength (seals)))) (PreH15 : ((Zlength (xs_spec)) = n_pre)) (PreH16 : ((Zlength (ys_spec)) = n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH18 : (0 <= i)) (PreH19 : (i < j)) (PreH20 : (j < n_pre)) (PreH21 : (0 <= ri)) (PreH22 : (ri < 2)) (PreH23 : (0 <= rj)) (PreH24 : (rj <= 2)) (PreH25 : (0 <= best)) (PreH26 : (best <= 20000)) (PreH27 : (BestBefore paper seals i j ri rj best )) ,
  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (1 <= (Znth i xs_spec 0)) ” 
  &&  “ ((Znth i xs_spec 0) <= 100) ” 
  &&  “ (1 <= (Znth i ys_spec 0)) ” 
  &&  “ ((Znth i ys_spec 0) <= 100) ” 
  &&  “ (1 <= (Znth j ys_spec 0)) ” 
  &&  “ ((Znth j ys_spec 0) <= 100) ” 
  &&  “ (1 <= (Znth j xs_spec 0)) ” 
  &&  “ ((Znth j xs_spec 0) <= 100) ” 
  &&  “ (1 <= a_pre) ” 
  &&  “ (a_pre <= 100) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (b_pre <= 100) ”
.

Definition solver_partial_solve_wit_15_aux := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (rj <> 0)) (PreH2 : (rj <> 0)) (PreH3 : (ri = 0)) (PreH4 : (ri = 0)) (PreH5 : (rj < 2)) (PreH6 : (1 <= (fst (paper)))) (PreH7 : ((fst (paper)) <= 100)) (PreH8 : (1 <= (snd (paper)))) (PreH9 : ((snd (paper)) <= 100)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : ((fst (paper)) = a_pre)) (PreH13 : ((snd (paper)) = b_pre)) (PreH14 : (n_pre = (Zlength (seals)))) (PreH15 : ((Zlength (xs_spec)) = n_pre)) (PreH16 : ((Zlength (ys_spec)) = n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH18 : (0 <= i)) (PreH19 : (i < j)) (PreH20 : (j < n_pre)) (PreH21 : (0 <= ri)) (PreH22 : (ri < 2)) (PreH23 : (0 <= rj)) (PreH24 : (rj <= 2)) (PreH25 : (0 <= best)) (PreH26 : (best <= 20000)) (PreH27 : (BestBefore paper seals i j ri rj best )) ,
  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
|--
  “ (1 <= (Znth i xs_spec 0)) ” 
  &&  “ ((Znth i xs_spec 0) <= 100) ” 
  &&  “ (1 <= (Znth i ys_spec 0)) ” 
  &&  “ ((Znth i ys_spec 0) <= 100) ” 
  &&  “ (1 <= (Znth j ys_spec 0)) ” 
  &&  “ ((Znth j ys_spec 0) <= 100) ” 
  &&  “ (1 <= (Znth j xs_spec 0)) ” 
  &&  “ ((Znth j xs_spec 0) <= 100) ” 
  &&  “ (1 <= a_pre) ” 
  &&  “ (a_pre <= 100) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (b_pre <= 100) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (rj <> 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ”
  &&  (IntArray.full x_pre n_pre xs_spec )
  **  (IntArray.full y_pre n_pre ys_spec )
.

Definition solver_partial_solve_wit_15 := solver_partial_solve_wit_15_pure -> solver_partial_solve_wit_15_aux.

Definition solver_partial_solve_wit_16_pure := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (rj = 0)) (PreH2 : (rj = 0)) (PreH3 : (ri = 0)) (PreH4 : (ri = 0)) (PreH5 : (rj < 2)) (PreH6 : (1 <= (fst (paper)))) (PreH7 : ((fst (paper)) <= 100)) (PreH8 : (1 <= (snd (paper)))) (PreH9 : ((snd (paper)) <= 100)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : ((fst (paper)) = a_pre)) (PreH13 : ((snd (paper)) = b_pre)) (PreH14 : (n_pre = (Zlength (seals)))) (PreH15 : ((Zlength (xs_spec)) = n_pre)) (PreH16 : ((Zlength (ys_spec)) = n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH18 : (0 <= i)) (PreH19 : (i < j)) (PreH20 : (j < n_pre)) (PreH21 : (0 <= ri)) (PreH22 : (ri < 2)) (PreH23 : (0 <= rj)) (PreH24 : (rj <= 2)) (PreH25 : (0 <= best)) (PreH26 : (best <= 20000)) (PreH27 : (BestBefore paper seals i j ri rj best )) ,
  (IntArray.full y_pre n_pre ys_spec )
  **  ((( &( "h2" ) )) # Int  |-> (Znth j ys_spec 0))
  **  (IntArray.full x_pre n_pre xs_spec )
  **  ((( &( "w2" ) )) # Int  |-> (Znth j xs_spec 0))
  **  ((( &( "h1" ) )) # Int  |-> (Znth i ys_spec 0))
  **  ((( &( "w1" ) )) # Int  |-> (Znth i xs_spec 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ri" ) )) # Int  |-> ri)
  **  ((( &( "rj" ) )) # Int  |-> rj)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (1 <= (Znth i xs_spec 0)) ” 
  &&  “ ((Znth i xs_spec 0) <= 100) ” 
  &&  “ (1 <= (Znth i ys_spec 0)) ” 
  &&  “ ((Znth i ys_spec 0) <= 100) ” 
  &&  “ (1 <= (Znth j xs_spec 0)) ” 
  &&  “ ((Znth j xs_spec 0) <= 100) ” 
  &&  “ (1 <= (Znth j ys_spec 0)) ” 
  &&  “ ((Znth j ys_spec 0) <= 100) ” 
  &&  “ (1 <= a_pre) ” 
  &&  “ (a_pre <= 100) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (b_pre <= 100) ”
.

Definition solver_partial_solve_wit_16_aux := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (seals: (@list (Z * Z))) (paper: (Z * Z)) (best: Z) (rj: Z) (ri: Z) (j: Z) (i: Z) (ys_spec: (@list Z)) (xs_spec: (@list Z))  __default__Prod_Z_Z (PreH1 : (rj = 0)) (PreH2 : (rj = 0)) (PreH3 : (ri = 0)) (PreH4 : (ri = 0)) (PreH5 : (rj < 2)) (PreH6 : (1 <= (fst (paper)))) (PreH7 : ((fst (paper)) <= 100)) (PreH8 : (1 <= (snd (paper)))) (PreH9 : ((snd (paper)) <= 100)) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : ((fst (paper)) = a_pre)) (PreH13 : ((snd (paper)) = b_pre)) (PreH14 : (n_pre = (Zlength (seals)))) (PreH15 : ((Zlength (xs_spec)) = n_pre)) (PreH16 : ((Zlength (ys_spec)) = n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z))))))) (PreH18 : (0 <= i)) (PreH19 : (i < j)) (PreH20 : (j < n_pre)) (PreH21 : (0 <= ri)) (PreH22 : (ri < 2)) (PreH23 : (0 <= rj)) (PreH24 : (rj <= 2)) (PreH25 : (0 <= best)) (PreH26 : (best <= 20000)) (PreH27 : (BestBefore paper seals i j ri rj best )) ,
  (IntArray.full y_pre n_pre ys_spec )
  **  (IntArray.full x_pre n_pre xs_spec )
|--
  “ (1 <= (Znth i xs_spec 0)) ” 
  &&  “ ((Znth i xs_spec 0) <= 100) ” 
  &&  “ (1 <= (Znth i ys_spec 0)) ” 
  &&  “ ((Znth i ys_spec 0) <= 100) ” 
  &&  “ (1 <= (Znth j xs_spec 0)) ” 
  &&  “ ((Znth j xs_spec 0) <= 100) ” 
  &&  “ (1 <= (Znth j ys_spec 0)) ” 
  &&  “ ((Znth j ys_spec 0) <= 100) ” 
  &&  “ (1 <= a_pre) ” 
  &&  “ (a_pre <= 100) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (b_pre <= 100) ” 
  &&  “ (rj = 0) ” 
  &&  “ (rj = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (ri = 0) ” 
  &&  “ (rj < 2) ” 
  &&  “ (1 <= (fst (paper))) ” 
  &&  “ ((fst (paper)) <= 100) ” 
  &&  “ (1 <= (snd (paper))) ” 
  &&  “ ((snd (paper)) <= 100) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ ((fst (paper)) = a_pre) ” 
  &&  “ ((snd (paper)) = b_pre) ” 
  &&  “ (n_pre = (Zlength (seals))) ” 
  &&  “ ((Zlength (xs_spec)) = n_pre) ” 
  &&  “ ((Zlength (ys_spec)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((Znth k seals __default__Prod_Z_Z)))) /\ ((fst ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ (1 <= (snd ((Znth k seals __default__Prod_Z_Z))))) /\ ((snd ((Znth k seals __default__Prod_Z_Z))) <= 100)) /\ ((Znth k xs_spec 0) = (fst ((Znth k seals __default__Prod_Z_Z))))) /\ ((Znth k ys_spec 0) = (snd ((Znth k seals __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= ri) ” 
  &&  “ (ri < 2) ” 
  &&  “ (0 <= rj) ” 
  &&  “ (rj <= 2) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 20000) ” 
  &&  “ (BestBefore paper seals i j ri rj best ) ”
  &&  (IntArray.full y_pre n_pre ys_spec )
  **  (IntArray.full x_pre n_pre xs_spec )
.

Definition solver_partial_solve_wit_16 := solver_partial_solve_wit_16_pure -> solver_partial_solve_wit_16_aux.

Module Type VC_Correct.


Axiom proof_of_fits_safety_wit_1 : fits_safety_wit_1.
Axiom proof_of_fits_safety_wit_2 : fits_safety_wit_2.
Axiom proof_of_fits_safety_wit_3 : fits_safety_wit_3.
Axiom proof_of_fits_safety_wit_4 : fits_safety_wit_4.
Axiom proof_of_fits_safety_wit_5 : fits_safety_wit_5.
Axiom proof_of_fits_safety_wit_6 : fits_safety_wit_6.
Axiom proof_of_fits_safety_wit_7 : fits_safety_wit_7.
Axiom proof_of_fits_safety_wit_8 : fits_safety_wit_8.
Axiom proof_of_fits_safety_wit_9 : fits_safety_wit_9.
Axiom proof_of_fits_safety_wit_10 : fits_safety_wit_10.
Axiom proof_of_fits_safety_wit_11 : fits_safety_wit_11.
Axiom proof_of_fits_safety_wit_12 : fits_safety_wit_12.
Axiom proof_of_fits_safety_wit_13 : fits_safety_wit_13.
Axiom proof_of_fits_safety_wit_14 : fits_safety_wit_14.
Axiom proof_of_fits_safety_wit_15 : fits_safety_wit_15.
Axiom proof_of_fits_return_wit_1 : fits_return_wit_1.
Axiom proof_of_fits_return_wit_2 : fits_return_wit_2.
Axiom proof_of_fits_return_wit_3 : fits_return_wit_3.
Axiom proof_of_fits_return_wit_4 : fits_return_wit_4.
Axiom proof_of_fits_return_wit_5 : fits_return_wit_5.
Axiom proof_of_fits_return_wit_6 : fits_return_wit_6.
Axiom proof_of_fits_return_wit_7 : fits_return_wit_7.
Axiom proof_of_fits_return_wit_8 : fits_return_wit_8.
Axiom proof_of_fits_return_wit_9 : fits_return_wit_9.
Axiom proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Axiom proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Axiom proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Axiom proof_of_solver_safety_wit_4 : solver_safety_wit_4.
Axiom proof_of_solver_safety_wit_5 : solver_safety_wit_5.
Axiom proof_of_solver_safety_wit_6 : solver_safety_wit_6.
Axiom proof_of_solver_safety_wit_7 : solver_safety_wit_7.
Axiom proof_of_solver_safety_wit_8 : solver_safety_wit_8.
Axiom proof_of_solver_safety_wit_9 : solver_safety_wit_9.
Axiom proof_of_solver_safety_wit_10 : solver_safety_wit_10.
Axiom proof_of_solver_safety_wit_11 : solver_safety_wit_11.
Axiom proof_of_solver_safety_wit_12 : solver_safety_wit_12.
Axiom proof_of_solver_safety_wit_13 : solver_safety_wit_13.
Axiom proof_of_solver_safety_wit_14 : solver_safety_wit_14.
Axiom proof_of_solver_safety_wit_15 : solver_safety_wit_15.
Axiom proof_of_solver_safety_wit_16 : solver_safety_wit_16.
Axiom proof_of_solver_safety_wit_17 : solver_safety_wit_17.
Axiom proof_of_solver_safety_wit_18 : solver_safety_wit_18.
Axiom proof_of_solver_safety_wit_19 : solver_safety_wit_19.
Axiom proof_of_solver_safety_wit_20 : solver_safety_wit_20.
Axiom proof_of_solver_safety_wit_21 : solver_safety_wit_21.
Axiom proof_of_solver_safety_wit_22 : solver_safety_wit_22.
Axiom proof_of_solver_safety_wit_23 : solver_safety_wit_23.
Axiom proof_of_solver_safety_wit_24 : solver_safety_wit_24.
Axiom proof_of_solver_safety_wit_25 : solver_safety_wit_25.
Axiom proof_of_solver_safety_wit_26 : solver_safety_wit_26.
Axiom proof_of_solver_safety_wit_27 : solver_safety_wit_27.
Axiom proof_of_solver_safety_wit_28 : solver_safety_wit_28.
Axiom proof_of_solver_safety_wit_29 : solver_safety_wit_29.
Axiom proof_of_solver_safety_wit_30 : solver_safety_wit_30.
Axiom proof_of_solver_safety_wit_31 : solver_safety_wit_31.
Axiom proof_of_solver_safety_wit_32 : solver_safety_wit_32.
Axiom proof_of_solver_safety_wit_33 : solver_safety_wit_33.
Axiom proof_of_solver_safety_wit_34 : solver_safety_wit_34.
Axiom proof_of_solver_safety_wit_35 : solver_safety_wit_35.
Axiom proof_of_solver_safety_wit_36 : solver_safety_wit_36.
Axiom proof_of_solver_safety_wit_37 : solver_safety_wit_37.
Axiom proof_of_solver_safety_wit_38 : solver_safety_wit_38.
Axiom proof_of_solver_safety_wit_39 : solver_safety_wit_39.
Axiom proof_of_solver_safety_wit_40 : solver_safety_wit_40.
Axiom proof_of_solver_safety_wit_41 : solver_safety_wit_41.
Axiom proof_of_solver_safety_wit_42 : solver_safety_wit_42.
Axiom proof_of_solver_safety_wit_43 : solver_safety_wit_43.
Axiom proof_of_solver_safety_wit_44 : solver_safety_wit_44.
Axiom proof_of_solver_safety_wit_45 : solver_safety_wit_45.
Axiom proof_of_solver_safety_wit_46 : solver_safety_wit_46.
Axiom proof_of_solver_safety_wit_47 : solver_safety_wit_47.
Axiom proof_of_solver_safety_wit_48 : solver_safety_wit_48.
Axiom proof_of_solver_safety_wit_49 : solver_safety_wit_49.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Axiom proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Axiom proof_of_solver_entail_wit_5_3 : solver_entail_wit_5_3.
Axiom proof_of_solver_entail_wit_5_4 : solver_entail_wit_5_4.
Axiom proof_of_solver_entail_wit_5_5 : solver_entail_wit_5_5.
Axiom proof_of_solver_entail_wit_5_6 : solver_entail_wit_5_6.
Axiom proof_of_solver_entail_wit_5_7 : solver_entail_wit_5_7.
Axiom proof_of_solver_entail_wit_5_8 : solver_entail_wit_5_8.
Axiom proof_of_solver_entail_wit_6_1 : solver_entail_wit_6_1.
Axiom proof_of_solver_entail_wit_6_2 : solver_entail_wit_6_2.
Axiom proof_of_solver_entail_wit_6_3 : solver_entail_wit_6_3.
Axiom proof_of_solver_entail_wit_6_4 : solver_entail_wit_6_4.
Axiom proof_of_solver_entail_wit_6_5 : solver_entail_wit_6_5.
Axiom proof_of_solver_entail_wit_6_6 : solver_entail_wit_6_6.
Axiom proof_of_solver_entail_wit_6_7 : solver_entail_wit_6_7.
Axiom proof_of_solver_entail_wit_6_8 : solver_entail_wit_6_8.
Axiom proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Axiom proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Axiom proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Axiom proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1.
Axiom proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2.
Axiom proof_of_solver_entail_wit_10_3 : solver_entail_wit_10_3.
Axiom proof_of_solver_entail_wit_10_4 : solver_entail_wit_10_4.
Axiom proof_of_solver_entail_wit_10_5 : solver_entail_wit_10_5.
Axiom proof_of_solver_entail_wit_10_6 : solver_entail_wit_10_6.
Axiom proof_of_solver_entail_wit_10_7 : solver_entail_wit_10_7.
Axiom proof_of_solver_entail_wit_10_8 : solver_entail_wit_10_8.
Axiom proof_of_solver_entail_wit_10_9 : solver_entail_wit_10_9.
Axiom proof_of_solver_entail_wit_10_10 : solver_entail_wit_10_10.
Axiom proof_of_solver_entail_wit_10_11 : solver_entail_wit_10_11.
Axiom proof_of_solver_entail_wit_10_12 : solver_entail_wit_10_12.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.
Axiom proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8.
Axiom proof_of_solver_partial_solve_wit_9 : solver_partial_solve_wit_9.
Axiom proof_of_solver_partial_solve_wit_10 : solver_partial_solve_wit_10.
Axiom proof_of_solver_partial_solve_wit_11 : solver_partial_solve_wit_11.
Axiom proof_of_solver_partial_solve_wit_12 : solver_partial_solve_wit_12.
Axiom proof_of_solver_partial_solve_wit_13_pure : solver_partial_solve_wit_13_pure.
Axiom proof_of_solver_partial_solve_wit_13 : solver_partial_solve_wit_13.
Axiom proof_of_solver_partial_solve_wit_14_pure : solver_partial_solve_wit_14_pure.
Axiom proof_of_solver_partial_solve_wit_14 : solver_partial_solve_wit_14.
Axiom proof_of_solver_partial_solve_wit_15_pure : solver_partial_solve_wit_15_pure.
Axiom proof_of_solver_partial_solve_wit_15 : solver_partial_solve_wit_15.
Axiom proof_of_solver_partial_solve_wit_16_pure : solver_partial_solve_wit_16_pure.
Axiom proof_of_solver_partial_solve_wit_16 : solver_partial_solve_wit_16.

End VC_Correct.
