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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P056_65B_harry_potter_and_the_history_of_magic_lib.
Local Open Scope sac.

(*----- Function next_year -----*)

Definition next_year_safety_wit_1 := 
forall (prev_pre: Z) (y_pre: Z) (PreH1 : (1000 <= y_pre)) (PreH2 : (y_pre <= 9999)) (PreH3 : (1000 <= prev_pre)) (PreH4 : (prev_pre <= 2011)) ,
  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
|--
  “ ((y_pre <> (INT_MIN)) \/ (1000 <> (-1))) ” 
  &&  “ (1000 <> 0) ”
.

Definition next_year_safety_wit_2 := 
forall (prev_pre: Z) (y_pre: Z) (PreH1 : (1000 <= y_pre)) (PreH2 : (y_pre <= 9999)) (PreH3 : (1000 <= prev_pre)) (PreH4 : (prev_pre <= 2011)) ,
  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
|--
  “ (((y_pre ÷ 100 ) <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition next_year_safety_wit_3 := 
forall (prev_pre: Z) (y_pre: Z) (PreH1 : (1000 <= y_pre)) (PreH2 : (y_pre <= 9999)) (PreH3 : (1000 <= prev_pre)) (PreH4 : (prev_pre <= 2011)) ,
  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
|--
  “ ((y_pre <> (INT_MIN)) \/ (100 <> (-1))) ” 
  &&  “ (100 <> 0) ”
.

Definition next_year_safety_wit_4 := 
forall (prev_pre: Z) (y_pre: Z) (PreH1 : (1000 <= y_pre)) (PreH2 : (y_pre <= 9999)) (PreH3 : (1000 <= prev_pre)) (PreH4 : (prev_pre <= 2011)) ,
  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
|--
  “ (((y_pre ÷ 10 ) <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition next_year_safety_wit_5 := 
forall (prev_pre: Z) (y_pre: Z) (PreH1 : (1000 <= y_pre)) (PreH2 : (y_pre <= 9999)) (PreH3 : (1000 <= prev_pre)) (PreH4 : (prev_pre <= 2011)) ,
  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
|--
  “ ((y_pre <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition next_year_safety_wit_6 := 
forall (prev_pre: Z) (y_pre: Z) (PreH1 : (1000 <= y_pre)) (PreH2 : (y_pre <= 9999)) (PreH3 : (1000 <= prev_pre)) (PreH4 : (prev_pre <= 2011)) ,
  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
|--
  “ ((y_pre <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition next_year_safety_wit_7 := 
forall (prev_pre: Z) (y_pre: Z) (PreH1 : (1000 <= y_pre)) (PreH2 : (y_pre <= 9999)) (PreH3 : (1000 <= prev_pre)) (PreH4 : (prev_pre <= 2011)) ,
  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition next_year_safety_wit_8 := 
forall (prev_pre: Z) (y_pre: Z) (PreH1 : (1000 <= y_pre)) (PreH2 : (y_pre <= 9999)) (PreH3 : (1000 <= prev_pre)) (PreH4 : (prev_pre <= 2011)) ,
  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition next_year_safety_wit_9 := 
forall (prev_pre: Z) (y_pre: Z) (PreH1 : (1000 <= y_pre)) (PreH2 : (y_pre <= 9999)) (PreH3 : (1000 <= prev_pre)) (PreH4 : (prev_pre <= 2011)) ,
  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition next_year_safety_wit_10 := 
forall (prev_pre: Z) (y_pre: Z) (PreH1 : (1000 <= y_pre)) (PreH2 : (y_pre <= 9999)) (PreH3 : (1000 <= prev_pre)) (PreH4 : (prev_pre <= 2011)) ,
  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
|--
  “ (100 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 100) ”
.

Definition next_year_safety_wit_11 := 
forall (prev_pre: Z) (y_pre: Z) (PreH1 : (1000 <= y_pre)) (PreH2 : (y_pre <= 9999)) (PreH3 : (1000 <= prev_pre)) (PreH4 : (prev_pre <= 2011)) ,
  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition next_year_safety_wit_12 := 
forall (prev_pre: Z) (y_pre: Z) (PreH1 : (1000 <= y_pre)) (PreH2 : (y_pre <= 9999)) (PreH3 : (1000 <= prev_pre)) (PreH4 : (prev_pre <= 2011)) ,
  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
|--
  “ (1000 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000) ”
.

Definition next_year_safety_wit_13 := 
forall (prev_pre: Z) (y_pre: Z) (PreH1 : (1000 <= y_pre)) (PreH2 : (y_pre <= 9999)) (PreH3 : (1000 <= prev_pre)) (PreH4 : (prev_pre <= 2011)) ,
  ((( &( "best" ) )) # Int  |->_)
  **  (IntArray.full ( &( "d" ) ) 4 (cons ((y_pre ÷ 1000 )) ((cons (((y_pre ÷ 100 ) % ( 10 ) )) ((cons (((y_pre ÷ 10 ) % ( 10 ) )) ((cons ((y_pre % ( 10 ) )) ((@nil Z))))))))) )
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition next_year_safety_wit_14 := 
forall (prev_pre: Z) (y_pre: Z) (PreH1 : (1000 <= y_pre)) (PreH2 : (y_pre <= 9999)) (PreH3 : (1000 <= prev_pre)) (PreH4 : (prev_pre <= 2011)) ,
  ((( &( "best" ) )) # Int  |->_)
  **  (IntArray.full ( &( "d" ) ) 4 (cons ((y_pre ÷ 1000 )) ((cons (((y_pre ÷ 100 ) % ( 10 ) )) ((cons (((y_pre ÷ 10 ) % ( 10 ) )) ((cons ((y_pre % ( 10 ) )) ((@nil Z))))))))) )
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition next_year_safety_wit_15 := 
forall (prev_pre: Z) (y_pre: Z) (PreH1 : (1000 <= y_pre)) (PreH2 : (y_pre <= 9999)) (PreH3 : (1000 <= prev_pre)) (PreH4 : (prev_pre <= 2011)) ,
  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |-> (-1))
  **  (IntArray.full ( &( "d" ) ) 4 (cons ((y_pre ÷ 1000 )) ((cons (((y_pre ÷ 100 ) % ( 10 ) )) ((cons (((y_pre ÷ 10 ) % ( 10 ) )) ((cons ((y_pre % ( 10 ) )) ((@nil Z))))))))) )
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition next_year_safety_wit_16 := 
forall (prev_pre: Z) (y_pre: Z) (best: Z) (pos: Z) (PreH1 : (1000 <= y_pre)) (PreH2 : (y_pre <= 9999)) (PreH3 : (1000 <= prev_pre)) (PreH4 : (prev_pre <= 2011)) (PreH5 : (0 <= pos)) (PreH6 : (pos <= 4)) (PreH7 : ((-1) <= best)) (PreH8 : (best <= 2011)) (PreH9 : (BestScanned y_pre prev_pre pos (DigitLower (pos)) best )) (PreH10 : (0 <= (Znth 0 (YearDigits (y_pre)) 0))) (PreH11 : ((Znth 0 (YearDigits (y_pre)) 0) <= 9)) (PreH12 : (0 <= (Znth 1 (YearDigits (y_pre)) 0))) (PreH13 : ((Znth 1 (YearDigits (y_pre)) 0) <= 9)) (PreH14 : (0 <= (Znth 2 (YearDigits (y_pre)) 0))) (PreH15 : ((Znth 2 (YearDigits (y_pre)) 0) <= 9)) (PreH16 : (0 <= (Znth 3 (YearDigits (y_pre)) 0))) (PreH17 : ((Znth 3 (YearDigits (y_pre)) 0) <= 9)) ,
  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full ( &( "d" ) ) 4 (YearDigits (y_pre)) )
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition next_year_safety_wit_17 := 
forall (prev_pre: Z) (y_pre: Z) (best: Z) (pos: Z) (PreH1 : (pos < 4)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos <= 4)) (PreH8 : ((-1) <= best)) (PreH9 : (best <= 2011)) (PreH10 : (BestScanned y_pre prev_pre pos (DigitLower (pos)) best )) (PreH11 : (0 <= (Znth 0 (YearDigits (y_pre)) 0))) (PreH12 : ((Znth 0 (YearDigits (y_pre)) 0) <= 9)) (PreH13 : (0 <= (Znth 1 (YearDigits (y_pre)) 0))) (PreH14 : ((Znth 1 (YearDigits (y_pre)) 0) <= 9)) (PreH15 : (0 <= (Znth 2 (YearDigits (y_pre)) 0))) (PreH16 : ((Znth 2 (YearDigits (y_pre)) 0) <= 9)) (PreH17 : (0 <= (Znth 3 (YearDigits (y_pre)) 0))) (PreH18 : ((Znth 3 (YearDigits (y_pre)) 0) <= 9)) ,
  ((( &( "v" ) )) # Int  |->_)
  **  (IntArray.full ( &( "d" ) ) 4 (YearDigits (y_pre)) )
  **  ((( &( "old" ) )) # Int  |-> (Znth pos (YearDigits (y_pre)) 0))
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition next_year_safety_wit_18 := 
forall (prev_pre: Z) (y_pre: Z) (best: Z) (pos: Z) (PreH1 : (pos = 0)) (PreH2 : (pos < 4)) (PreH3 : (1000 <= y_pre)) (PreH4 : (y_pre <= 9999)) (PreH5 : (1000 <= prev_pre)) (PreH6 : (prev_pre <= 2011)) (PreH7 : (0 <= pos)) (PreH8 : (pos <= 4)) (PreH9 : ((-1) <= best)) (PreH10 : (best <= 2011)) (PreH11 : (BestScanned y_pre prev_pre pos (DigitLower (pos)) best )) (PreH12 : (0 <= (Znth 0 (YearDigits (y_pre)) 0))) (PreH13 : ((Znth 0 (YearDigits (y_pre)) 0) <= 9)) (PreH14 : (0 <= (Znth 1 (YearDigits (y_pre)) 0))) (PreH15 : ((Znth 1 (YearDigits (y_pre)) 0) <= 9)) (PreH16 : (0 <= (Znth 2 (YearDigits (y_pre)) 0))) (PreH17 : ((Znth 2 (YearDigits (y_pre)) 0) <= 9)) (PreH18 : (0 <= (Znth 3 (YearDigits (y_pre)) 0))) (PreH19 : ((Znth 3 (YearDigits (y_pre)) 0) <= 9)) ,
  ((( &( "v" ) )) # Int  |->_)
  **  (IntArray.full ( &( "d" ) ) 4 (YearDigits (y_pre)) )
  **  ((( &( "old" ) )) # Int  |-> (Znth pos (YearDigits (y_pre)) 0))
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition next_year_safety_wit_19 := 
forall (prev_pre: Z) (y_pre: Z) (best: Z) (pos: Z) (PreH1 : (pos <> 0)) (PreH2 : (pos < 4)) (PreH3 : (1000 <= y_pre)) (PreH4 : (y_pre <= 9999)) (PreH5 : (1000 <= prev_pre)) (PreH6 : (prev_pre <= 2011)) (PreH7 : (0 <= pos)) (PreH8 : (pos <= 4)) (PreH9 : ((-1) <= best)) (PreH10 : (best <= 2011)) (PreH11 : (BestScanned y_pre prev_pre pos (DigitLower (pos)) best )) (PreH12 : (0 <= (Znth 0 (YearDigits (y_pre)) 0))) (PreH13 : ((Znth 0 (YearDigits (y_pre)) 0) <= 9)) (PreH14 : (0 <= (Znth 1 (YearDigits (y_pre)) 0))) (PreH15 : ((Znth 1 (YearDigits (y_pre)) 0) <= 9)) (PreH16 : (0 <= (Znth 2 (YearDigits (y_pre)) 0))) (PreH17 : ((Znth 2 (YearDigits (y_pre)) 0) <= 9)) (PreH18 : (0 <= (Znth 3 (YearDigits (y_pre)) 0))) (PreH19 : ((Znth 3 (YearDigits (y_pre)) 0) <= 9)) ,
  ((( &( "v" ) )) # Int  |->_)
  **  (IntArray.full ( &( "d" ) ) 4 (YearDigits (y_pre)) )
  **  ((( &( "old" ) )) # Int  |-> (Znth pos (YearDigits (y_pre)) 0))
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition next_year_safety_wit_20 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (1000 <= y_pre)) (PreH2 : (y_pre <= 9999)) (PreH3 : (1000 <= prev_pre)) (PreH4 : (prev_pre <= 2011)) (PreH5 : (0 <= pos)) (PreH6 : (pos < 4)) (PreH7 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH8 : ((DigitLower (pos)) <= v)) (PreH9 : (v <= 10)) (PreH10 : ((-1) <= best)) (PreH11 : (best <= 2011)) (PreH12 : (BestScanned y_pre prev_pre pos v best )) (PreH13 : (v = (DigitLower (pos)))) (PreH14 : (digits = (YearDigits (y_pre)))) (PreH15 : (0 <= (Znth 0 digits 0))) (PreH16 : ((Znth 0 digits 0) <= 9)) (PreH17 : (0 <= (Znth 1 digits 0))) (PreH18 : ((Znth 1 digits 0) <= 9)) (PreH19 : (0 <= (Znth 2 digits 0))) (PreH20 : ((Znth 2 digits 0) <= 9)) (PreH21 : (0 <= (Znth 3 digits 0))) (PreH22 : ((Znth 3 digits 0) <= 9)) ,
  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full ( &( "d" ) ) 4 digits )
|--
  “ (9 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 9) ”
.

Definition next_year_safety_wit_21 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (1000 <= y_pre)) (PreH2 : (y_pre <= 9999)) (PreH3 : (1000 <= prev_pre)) (PreH4 : (prev_pre <= 2011)) (PreH5 : (0 <= pos)) (PreH6 : (pos < 4)) (PreH7 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH8 : ((DigitLower (pos)) <= v)) (PreH9 : (v <= 10)) (PreH10 : ((-1) <= best)) (PreH11 : (best <= 2011)) (PreH12 : (BestScanned y_pre prev_pre pos v best )) (PreH13 : ((DigitLower (pos)) < v)) (PreH14 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH15 : (0 <= (Znth 0 digits 0))) (PreH16 : ((Znth 0 digits 0) <= 9)) (PreH17 : (0 <= (Znth 1 digits 0))) (PreH18 : ((Znth 1 digits 0) <= 9)) (PreH19 : (0 <= (Znth 2 digits 0))) (PreH20 : ((Znth 2 digits 0) <= 9)) (PreH21 : (0 <= (Znth 3 digits 0))) (PreH22 : ((Znth 3 digits 0) <= 9)) ,
  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full ( &( "d" ) ) 4 digits )
|--
  “ (9 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 9) ”
.

Definition next_year_safety_wit_22 := 
(
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) )) ”
) \/
(
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) )) ”
).

Definition next_year_safety_wit_22_split_goal_1 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) <= INT_MAX) ”
.

Definition next_year_safety_wit_22_split_goal_2 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((INT_MIN) <= (((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) )) ”
.

Definition next_year_safety_wit_23 := 
(
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) )) ”
) \/
(
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) )) ”
).

Definition next_year_safety_wit_23_split_goal_1 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) <= INT_MAX) ”
.

Definition next_year_safety_wit_23_split_goal_2 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((INT_MIN) <= ((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) )) ”
.

Definition next_year_safety_wit_24 := 
(
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 )) ”
) \/
(
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 )) ”
).

Definition next_year_safety_wit_24_split_goal_1 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) <= INT_MAX) ”
.

Definition next_year_safety_wit_24_split_goal_2 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((INT_MIN) <= ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 )) ”
.

Definition next_year_safety_wit_25 := 
(
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) )) ”
) \/
(
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) )) ”
).

Definition next_year_safety_wit_25_split_goal_1 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) <= INT_MAX) ”
.

Definition next_year_safety_wit_25_split_goal_2 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((INT_MIN) <= (((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) )) ”
.

Definition next_year_safety_wit_26 := 
(
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 )) ”
) \/
(
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 )) ”
).

Definition next_year_safety_wit_26_split_goal_1 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) <= INT_MAX) ”
.

Definition next_year_safety_wit_26_split_goal_2 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((INT_MIN) <= ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 )) ”
.

Definition next_year_safety_wit_27 := 
(
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 )) ”
) \/
(
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 )) ”
).

Definition next_year_safety_wit_27_split_goal_1 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) <= INT_MAX) ”
.

Definition next_year_safety_wit_27_split_goal_2 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((INT_MIN) <= ((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 )) ”
.

Definition next_year_safety_wit_28 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  ((( &( "cand" ) )) # Int  |->_)
  **  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition next_year_safety_wit_29 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (1000 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000) ”
.

Definition next_year_safety_wit_30 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition next_year_safety_wit_31 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (100 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 100) ”
.

Definition next_year_safety_wit_32 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition next_year_safety_wit_33 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition next_year_safety_wit_34 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition next_year_safety_wit_35 := 
(
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) )) ”
) \/
(
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) )) ”
).

Definition next_year_safety_wit_35_split_goal_1 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) <= INT_MAX) ”
.

Definition next_year_safety_wit_35_split_goal_2 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((INT_MIN) <= (((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) )) ”
.

Definition next_year_safety_wit_36 := 
(
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) )) ”
) \/
(
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) )) ”
).

Definition next_year_safety_wit_36_split_goal_1 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) <= INT_MAX) ”
.

Definition next_year_safety_wit_36_split_goal_2 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((INT_MIN) <= ((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) )) ”
.

Definition next_year_safety_wit_37 := 
(
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 )) ”
) \/
(
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 )) ”
).

Definition next_year_safety_wit_37_split_goal_1 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) <= INT_MAX) ”
.

Definition next_year_safety_wit_37_split_goal_2 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((INT_MIN) <= ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 )) ”
.

Definition next_year_safety_wit_38 := 
(
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) )) ”
) \/
(
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) )) ”
).

Definition next_year_safety_wit_38_split_goal_1 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) <= INT_MAX) ”
.

Definition next_year_safety_wit_38_split_goal_2 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((INT_MIN) <= (((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) )) ”
.

Definition next_year_safety_wit_39 := 
(
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 )) ”
) \/
(
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 )) ”
).

Definition next_year_safety_wit_39_split_goal_1 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) <= INT_MAX) ”
.

Definition next_year_safety_wit_39_split_goal_2 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((INT_MIN) <= ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 )) ”
.

Definition next_year_safety_wit_40 := 
(
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 )) ”
) \/
(
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 )) ”
).

Definition next_year_safety_wit_40_split_goal_1 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) <= INT_MAX) ”
.

Definition next_year_safety_wit_40_split_goal_2 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((INT_MIN) <= ((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 )) ”
.

Definition next_year_safety_wit_41 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  ((( &( "cand" ) )) # Int  |->_)
  **  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition next_year_safety_wit_42 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (1000 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000) ”
.

Definition next_year_safety_wit_43 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition next_year_safety_wit_44 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (100 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 100) ”
.

Definition next_year_safety_wit_45 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition next_year_safety_wit_46 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition next_year_safety_wit_47 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition next_year_safety_wit_48 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |-> (((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ))
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (1000 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000) ”
.

Definition next_year_safety_wit_49 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |-> (((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ))
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (1000 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000) ”
.

Definition next_year_safety_wit_50 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) >= 1000)) (PreH2 : (v <= 9)) (PreH3 : (1000 <= y_pre)) (PreH4 : (y_pre <= 9999)) (PreH5 : (1000 <= prev_pre)) (PreH6 : (prev_pre <= 2011)) (PreH7 : (0 <= pos)) (PreH8 : (pos < 4)) (PreH9 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH10 : ((DigitLower (pos)) <= v)) (PreH11 : (v <= 10)) (PreH12 : ((-1) <= best)) (PreH13 : (best <= 2011)) (PreH14 : (BestScanned y_pre prev_pre pos v best )) (PreH15 : ((DigitLower (pos)) < v)) (PreH16 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH17 : (0 <= (Znth 0 digits 0))) (PreH18 : ((Znth 0 digits 0) <= 9)) (PreH19 : (0 <= (Znth 1 digits 0))) (PreH20 : ((Znth 1 digits 0) <= 9)) (PreH21 : (0 <= (Znth 2 digits 0))) (PreH22 : ((Znth 2 digits 0) <= 9)) (PreH23 : (0 <= (Znth 3 digits 0))) (PreH24 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |-> (((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ))
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (2011 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2011) ”
.

Definition next_year_safety_wit_51 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) >= 1000)) (PreH2 : (v <= 9)) (PreH3 : (1000 <= y_pre)) (PreH4 : (y_pre <= 9999)) (PreH5 : (1000 <= prev_pre)) (PreH6 : (prev_pre <= 2011)) (PreH7 : (0 <= pos)) (PreH8 : (pos < 4)) (PreH9 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH10 : ((DigitLower (pos)) <= v)) (PreH11 : (v <= 10)) (PreH12 : ((-1) <= best)) (PreH13 : (best <= 2011)) (PreH14 : (BestScanned y_pre prev_pre pos v best )) (PreH15 : (v = (DigitLower (pos)))) (PreH16 : (digits = (YearDigits (y_pre)))) (PreH17 : (0 <= (Znth 0 digits 0))) (PreH18 : ((Znth 0 digits 0) <= 9)) (PreH19 : (0 <= (Znth 1 digits 0))) (PreH20 : ((Znth 1 digits 0) <= 9)) (PreH21 : (0 <= (Znth 2 digits 0))) (PreH22 : ((Znth 2 digits 0) <= 9)) (PreH23 : (0 <= (Znth 3 digits 0))) (PreH24 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |-> (((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ))
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (2011 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2011) ”
.

Definition next_year_safety_wit_52 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) >= prev_pre)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) <= 2011)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) >= 1000)) (PreH4 : (v <= 9)) (PreH5 : (1000 <= y_pre)) (PreH6 : (y_pre <= 9999)) (PreH7 : (1000 <= prev_pre)) (PreH8 : (prev_pre <= 2011)) (PreH9 : (0 <= pos)) (PreH10 : (pos < 4)) (PreH11 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH12 : ((DigitLower (pos)) <= v)) (PreH13 : (v <= 10)) (PreH14 : ((-1) <= best)) (PreH15 : (best <= 2011)) (PreH16 : (BestScanned y_pre prev_pre pos v best )) (PreH17 : ((DigitLower (pos)) < v)) (PreH18 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH19 : (0 <= (Znth 0 digits 0))) (PreH20 : ((Znth 0 digits 0) <= 9)) (PreH21 : (0 <= (Znth 1 digits 0))) (PreH22 : ((Znth 1 digits 0) <= 9)) (PreH23 : (0 <= (Znth 2 digits 0))) (PreH24 : ((Znth 2 digits 0) <= 9)) (PreH25 : (0 <= (Znth 3 digits 0))) (PreH26 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |-> (((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ))
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition next_year_safety_wit_53 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) >= prev_pre)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) <= 2011)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) >= 1000)) (PreH4 : (v <= 9)) (PreH5 : (1000 <= y_pre)) (PreH6 : (y_pre <= 9999)) (PreH7 : (1000 <= prev_pre)) (PreH8 : (prev_pre <= 2011)) (PreH9 : (0 <= pos)) (PreH10 : (pos < 4)) (PreH11 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH12 : ((DigitLower (pos)) <= v)) (PreH13 : (v <= 10)) (PreH14 : ((-1) <= best)) (PreH15 : (best <= 2011)) (PreH16 : (BestScanned y_pre prev_pre pos v best )) (PreH17 : (v = (DigitLower (pos)))) (PreH18 : (digits = (YearDigits (y_pre)))) (PreH19 : (0 <= (Znth 0 digits 0))) (PreH20 : ((Znth 0 digits 0) <= 9)) (PreH21 : (0 <= (Znth 1 digits 0))) (PreH22 : ((Znth 1 digits 0) <= 9)) (PreH23 : (0 <= (Znth 2 digits 0))) (PreH24 : ((Znth 2 digits 0) <= 9)) (PreH25 : (0 <= (Znth 3 digits 0))) (PreH26 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "cand" ) )) # Int  |-> (((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ))
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition next_year_safety_wit_54 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : (v = (DigitLower (pos)))) (PreH20 : (digits = (YearDigits (y_pre)))) (PreH21 : (0 <= (Znth 0 digits 0))) (PreH22 : ((Znth 0 digits 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits 0))) (PreH24 : ((Znth 1 digits 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits 0))) (PreH26 : ((Znth 2 digits 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits 0))) (PreH28 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> (((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ))
|--
  “ ((v + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (v + 1 )) ”
.

Definition next_year_safety_wit_55 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : ((DigitLower (pos)) < v)) (PreH20 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH21 : (0 <= (Znth 0 digits 0))) (PreH22 : ((Znth 0 digits 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits 0))) (PreH24 : ((Znth 1 digits 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits 0))) (PreH26 : ((Znth 2 digits 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits 0))) (PreH28 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> (((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ))
|--
  “ ((v + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (v + 1 )) ”
.

Definition next_year_safety_wit_56 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (best < 0)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) >= prev_pre)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) <= 2011)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) >= 1000)) (PreH5 : (v <= 9)) (PreH6 : (1000 <= y_pre)) (PreH7 : (y_pre <= 9999)) (PreH8 : (1000 <= prev_pre)) (PreH9 : (prev_pre <= 2011)) (PreH10 : (0 <= pos)) (PreH11 : (pos < 4)) (PreH12 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH13 : ((DigitLower (pos)) <= v)) (PreH14 : (v <= 10)) (PreH15 : ((-1) <= best)) (PreH16 : (best <= 2011)) (PreH17 : (BestScanned y_pre prev_pre pos v best )) (PreH18 : ((DigitLower (pos)) < v)) (PreH19 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH20 : (0 <= (Znth 0 digits 0))) (PreH21 : ((Znth 0 digits 0) <= 9)) (PreH22 : (0 <= (Znth 1 digits 0))) (PreH23 : ((Znth 1 digits 0) <= 9)) (PreH24 : (0 <= (Znth 2 digits 0))) (PreH25 : ((Znth 2 digits 0) <= 9)) (PreH26 : (0 <= (Znth 3 digits 0))) (PreH27 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> (((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ))
|--
  “ ((v + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (v + 1 )) ”
.

Definition next_year_safety_wit_57 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (best < 0)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) >= prev_pre)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) <= 2011)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) >= 1000)) (PreH5 : (v <= 9)) (PreH6 : (1000 <= y_pre)) (PreH7 : (y_pre <= 9999)) (PreH8 : (1000 <= prev_pre)) (PreH9 : (prev_pre <= 2011)) (PreH10 : (0 <= pos)) (PreH11 : (pos < 4)) (PreH12 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH13 : ((DigitLower (pos)) <= v)) (PreH14 : (v <= 10)) (PreH15 : ((-1) <= best)) (PreH16 : (best <= 2011)) (PreH17 : (BestScanned y_pre prev_pre pos v best )) (PreH18 : (v = (DigitLower (pos)))) (PreH19 : (digits = (YearDigits (y_pre)))) (PreH20 : (0 <= (Znth 0 digits 0))) (PreH21 : ((Znth 0 digits 0) <= 9)) (PreH22 : (0 <= (Znth 1 digits 0))) (PreH23 : ((Znth 1 digits 0) <= 9)) (PreH24 : (0 <= (Znth 2 digits 0))) (PreH25 : ((Znth 2 digits 0) <= 9)) (PreH26 : (0 <= (Znth 3 digits 0))) (PreH27 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> (((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ))
|--
  “ ((v + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (v + 1 )) ”
.

Definition next_year_safety_wit_58 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) < prev_pre)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) <= 2011)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) >= 1000)) (PreH4 : (v <= 9)) (PreH5 : (1000 <= y_pre)) (PreH6 : (y_pre <= 9999)) (PreH7 : (1000 <= prev_pre)) (PreH8 : (prev_pre <= 2011)) (PreH9 : (0 <= pos)) (PreH10 : (pos < 4)) (PreH11 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH12 : ((DigitLower (pos)) <= v)) (PreH13 : (v <= 10)) (PreH14 : ((-1) <= best)) (PreH15 : (best <= 2011)) (PreH16 : (BestScanned y_pre prev_pre pos v best )) (PreH17 : ((DigitLower (pos)) < v)) (PreH18 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH19 : (0 <= (Znth 0 digits 0))) (PreH20 : ((Znth 0 digits 0) <= 9)) (PreH21 : (0 <= (Znth 1 digits 0))) (PreH22 : ((Znth 1 digits 0) <= 9)) (PreH23 : (0 <= (Znth 2 digits 0))) (PreH24 : ((Znth 2 digits 0) <= 9)) (PreH25 : (0 <= (Znth 3 digits 0))) (PreH26 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((v + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (v + 1 )) ”
.

Definition next_year_safety_wit_59 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) < prev_pre)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) <= 2011)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) >= 1000)) (PreH4 : (v <= 9)) (PreH5 : (1000 <= y_pre)) (PreH6 : (y_pre <= 9999)) (PreH7 : (1000 <= prev_pre)) (PreH8 : (prev_pre <= 2011)) (PreH9 : (0 <= pos)) (PreH10 : (pos < 4)) (PreH11 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH12 : ((DigitLower (pos)) <= v)) (PreH13 : (v <= 10)) (PreH14 : ((-1) <= best)) (PreH15 : (best <= 2011)) (PreH16 : (BestScanned y_pre prev_pre pos v best )) (PreH17 : (v = (DigitLower (pos)))) (PreH18 : (digits = (YearDigits (y_pre)))) (PreH19 : (0 <= (Znth 0 digits 0))) (PreH20 : ((Znth 0 digits 0) <= 9)) (PreH21 : (0 <= (Znth 1 digits 0))) (PreH22 : ((Znth 1 digits 0) <= 9)) (PreH23 : (0 <= (Znth 2 digits 0))) (PreH24 : ((Znth 2 digits 0) <= 9)) (PreH25 : (0 <= (Znth 3 digits 0))) (PreH26 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((v + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (v + 1 )) ”
.

Definition next_year_safety_wit_60 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) < 1000)) (PreH2 : (v <= 9)) (PreH3 : (1000 <= y_pre)) (PreH4 : (y_pre <= 9999)) (PreH5 : (1000 <= prev_pre)) (PreH6 : (prev_pre <= 2011)) (PreH7 : (0 <= pos)) (PreH8 : (pos < 4)) (PreH9 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH10 : ((DigitLower (pos)) <= v)) (PreH11 : (v <= 10)) (PreH12 : ((-1) <= best)) (PreH13 : (best <= 2011)) (PreH14 : (BestScanned y_pre prev_pre pos v best )) (PreH15 : ((DigitLower (pos)) < v)) (PreH16 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH17 : (0 <= (Znth 0 digits 0))) (PreH18 : ((Znth 0 digits 0) <= 9)) (PreH19 : (0 <= (Znth 1 digits 0))) (PreH20 : ((Znth 1 digits 0) <= 9)) (PreH21 : (0 <= (Znth 2 digits 0))) (PreH22 : ((Znth 2 digits 0) <= 9)) (PreH23 : (0 <= (Znth 3 digits 0))) (PreH24 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((v + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (v + 1 )) ”
.

Definition next_year_safety_wit_61 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) < 1000)) (PreH2 : (v <= 9)) (PreH3 : (1000 <= y_pre)) (PreH4 : (y_pre <= 9999)) (PreH5 : (1000 <= prev_pre)) (PreH6 : (prev_pre <= 2011)) (PreH7 : (0 <= pos)) (PreH8 : (pos < 4)) (PreH9 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH10 : ((DigitLower (pos)) <= v)) (PreH11 : (v <= 10)) (PreH12 : ((-1) <= best)) (PreH13 : (best <= 2011)) (PreH14 : (BestScanned y_pre prev_pre pos v best )) (PreH15 : (v = (DigitLower (pos)))) (PreH16 : (digits = (YearDigits (y_pre)))) (PreH17 : (0 <= (Znth 0 digits 0))) (PreH18 : ((Znth 0 digits 0) <= 9)) (PreH19 : (0 <= (Znth 1 digits 0))) (PreH20 : ((Znth 1 digits 0) <= 9)) (PreH21 : (0 <= (Znth 2 digits 0))) (PreH22 : ((Znth 2 digits 0) <= 9)) (PreH23 : (0 <= (Znth 3 digits 0))) (PreH24 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((v + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (v + 1 )) ”
.

Definition next_year_safety_wit_62 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) > 2011)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) >= 1000)) (PreH3 : (v <= 9)) (PreH4 : (1000 <= y_pre)) (PreH5 : (y_pre <= 9999)) (PreH6 : (1000 <= prev_pre)) (PreH7 : (prev_pre <= 2011)) (PreH8 : (0 <= pos)) (PreH9 : (pos < 4)) (PreH10 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH11 : ((DigitLower (pos)) <= v)) (PreH12 : (v <= 10)) (PreH13 : ((-1) <= best)) (PreH14 : (best <= 2011)) (PreH15 : (BestScanned y_pre prev_pre pos v best )) (PreH16 : (v = (DigitLower (pos)))) (PreH17 : (digits = (YearDigits (y_pre)))) (PreH18 : (0 <= (Znth 0 digits 0))) (PreH19 : ((Znth 0 digits 0) <= 9)) (PreH20 : (0 <= (Znth 1 digits 0))) (PreH21 : ((Znth 1 digits 0) <= 9)) (PreH22 : (0 <= (Znth 2 digits 0))) (PreH23 : ((Znth 2 digits 0) <= 9)) (PreH24 : (0 <= (Znth 3 digits 0))) (PreH25 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((v + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (v + 1 )) ”
.

Definition next_year_safety_wit_63 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) > 2011)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) >= 1000)) (PreH3 : (v <= 9)) (PreH4 : (1000 <= y_pre)) (PreH5 : (y_pre <= 9999)) (PreH6 : (1000 <= prev_pre)) (PreH7 : (prev_pre <= 2011)) (PreH8 : (0 <= pos)) (PreH9 : (pos < 4)) (PreH10 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH11 : ((DigitLower (pos)) <= v)) (PreH12 : (v <= 10)) (PreH13 : ((-1) <= best)) (PreH14 : (best <= 2011)) (PreH15 : (BestScanned y_pre prev_pre pos v best )) (PreH16 : ((DigitLower (pos)) < v)) (PreH17 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH18 : (0 <= (Znth 0 digits 0))) (PreH19 : ((Znth 0 digits 0) <= 9)) (PreH20 : (0 <= (Znth 1 digits 0))) (PreH21 : ((Znth 1 digits 0) <= 9)) (PreH22 : (0 <= (Znth 2 digits 0))) (PreH23 : ((Znth 2 digits 0) <= 9)) (PreH24 : (0 <= (Znth 3 digits 0))) (PreH25 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((v + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (v + 1 )) ”
.

Definition next_year_safety_wit_64 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) >= best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : (v = (DigitLower (pos)))) (PreH20 : (digits = (YearDigits (y_pre)))) (PreH21 : (0 <= (Znth 0 digits 0))) (PreH22 : ((Znth 0 digits 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits 0))) (PreH24 : ((Znth 1 digits 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits 0))) (PreH26 : ((Znth 2 digits 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits 0))) (PreH28 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((v + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (v + 1 )) ”
.

Definition next_year_safety_wit_65 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) >= best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : ((DigitLower (pos)) < v)) (PreH20 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH21 : (0 <= (Znth 0 digits 0))) (PreH22 : ((Znth 0 digits 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits 0))) (PreH24 : ((Znth 1 digits 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits 0))) (PreH26 : ((Znth 2 digits 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits 0))) (PreH28 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((v + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (v + 1 )) ”
.

Definition next_year_safety_wit_66 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v > 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (old) (digits)) )
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((pos + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pos + 1 )) ”
.

Definition next_year_safety_wit_67 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v > 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (old) (digits)) )
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((pos + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pos + 1 )) ”
.

Definition next_year_entail_wit_1 := 
(
forall (prev_pre: Z) (y_pre: Z) (PreH1 : (1000 <= y_pre)) (PreH2 : (y_pre <= 9999)) (PreH3 : (1000 <= prev_pre)) (PreH4 : (prev_pre <= 2011)) ,
  (IntArray.full ( &( "d" ) ) 4 (cons ((y_pre ÷ 1000 )) ((cons (((y_pre ÷ 100 ) % ( 10 ) )) ((cons (((y_pre ÷ 10 ) % ( 10 ) )) ((cons ((y_pre % ( 10 ) )) ((@nil Z))))))))) )
|--
  “ (1000 <= y_pre) ” 
  &&  “ (y_pre <= 9999) ” 
  &&  “ (1000 <= prev_pre) ” 
  &&  “ (prev_pre <= 2011) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 4) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= 2011) ” 
  &&  “ (BestScanned y_pre prev_pre 0 (DigitLower (0)) (-1) ) ” 
  &&  “ (0 <= (Znth 0 (YearDigits (y_pre)) 0)) ” 
  &&  “ ((Znth 0 (YearDigits (y_pre)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 (YearDigits (y_pre)) 0)) ” 
  &&  “ ((Znth 1 (YearDigits (y_pre)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 (YearDigits (y_pre)) 0)) ” 
  &&  “ ((Znth 2 (YearDigits (y_pre)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 (YearDigits (y_pre)) 0)) ” 
  &&  “ ((Znth 3 (YearDigits (y_pre)) 0) <= 9) ”
  &&  (IntArray.full ( &( "d" ) ) 4 (YearDigits (y_pre)) )
) \/
(
forall (prev_pre: Z) (y_pre: Z) (PreH1 : (1000 <= y_pre)) (PreH2 : (y_pre <= 9999)) (PreH3 : (1000 <= prev_pre)) (PreH4 : (prev_pre <= 2011)) ,
  TT && emp 
|--
  “ ((Znth 3 (YearDigits (y_pre)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 (YearDigits (y_pre)) 0)) ” 
  &&  “ ((Znth 2 (YearDigits (y_pre)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 (YearDigits (y_pre)) 0)) ” 
  &&  “ ((Znth 1 (YearDigits (y_pre)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 (YearDigits (y_pre)) 0)) ” 
  &&  “ ((Znth 0 (YearDigits (y_pre)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 0 (YearDigits (y_pre)) 0)) ” 
  &&  “ (BestScanned y_pre prev_pre 0 (DigitLower (0)) (-1) ) ” 
  &&  “ ((cons ((y_pre ÷ 1000 )) ((cons (((y_pre ÷ 100 ) % ( 10 ) )) ((cons (((y_pre ÷ 10 ) % ( 10 ) )) ((cons ((y_pre % ( 10 ) )) ((@nil Z))))))))) = (YearDigits (y_pre))) ”
  &&  emp
).

Definition next_year_entail_wit_1_split_goal_1 := 
forall (prev_pre: Z) (y_pre: Z) (PreH1 : (1000 <= y_pre)) (PreH2 : (y_pre <= 9999)) (PreH3 : (1000 <= prev_pre)) (PreH4 : (prev_pre <= 2011)) ,
  ((Znth 3 (YearDigits (y_pre)) 0) <= 9)
.

Definition next_year_entail_wit_1_split_goal_2 := 
forall (prev_pre: Z) (y_pre: Z) (PreH1 : (1000 <= y_pre)) (PreH2 : (y_pre <= 9999)) (PreH3 : (1000 <= prev_pre)) (PreH4 : (prev_pre <= 2011)) ,
  (0 <= (Znth 3 (YearDigits (y_pre)) 0))
.

Definition next_year_entail_wit_1_split_goal_3 := 
forall (prev_pre: Z) (y_pre: Z) (PreH1 : (1000 <= y_pre)) (PreH2 : (y_pre <= 9999)) (PreH3 : (1000 <= prev_pre)) (PreH4 : (prev_pre <= 2011)) ,
  ((Znth 2 (YearDigits (y_pre)) 0) <= 9)
.

Definition next_year_entail_wit_1_split_goal_4 := 
forall (prev_pre: Z) (y_pre: Z) (PreH1 : (1000 <= y_pre)) (PreH2 : (y_pre <= 9999)) (PreH3 : (1000 <= prev_pre)) (PreH4 : (prev_pre <= 2011)) ,
  (0 <= (Znth 2 (YearDigits (y_pre)) 0))
.

Definition next_year_entail_wit_1_split_goal_5 := 
forall (prev_pre: Z) (y_pre: Z) (PreH1 : (1000 <= y_pre)) (PreH2 : (y_pre <= 9999)) (PreH3 : (1000 <= prev_pre)) (PreH4 : (prev_pre <= 2011)) ,
  ((Znth 1 (YearDigits (y_pre)) 0) <= 9)
.

Definition next_year_entail_wit_1_split_goal_6 := 
forall (prev_pre: Z) (y_pre: Z) (PreH1 : (1000 <= y_pre)) (PreH2 : (y_pre <= 9999)) (PreH3 : (1000 <= prev_pre)) (PreH4 : (prev_pre <= 2011)) ,
  (0 <= (Znth 1 (YearDigits (y_pre)) 0))
.

Definition next_year_entail_wit_1_split_goal_7 := 
forall (prev_pre: Z) (y_pre: Z) (PreH1 : (1000 <= y_pre)) (PreH2 : (y_pre <= 9999)) (PreH3 : (1000 <= prev_pre)) (PreH4 : (prev_pre <= 2011)) ,
  ((Znth 0 (YearDigits (y_pre)) 0) <= 9)
.

Definition next_year_entail_wit_1_split_goal_8 := 
forall (prev_pre: Z) (y_pre: Z) (PreH1 : (1000 <= y_pre)) (PreH2 : (y_pre <= 9999)) (PreH3 : (1000 <= prev_pre)) (PreH4 : (prev_pre <= 2011)) ,
  (0 <= (Znth 0 (YearDigits (y_pre)) 0))
.

Definition next_year_entail_wit_1_split_goal_9 := 
forall (prev_pre: Z) (y_pre: Z) (PreH1 : (1000 <= y_pre)) (PreH2 : (y_pre <= 9999)) (PreH3 : (1000 <= prev_pre)) (PreH4 : (prev_pre <= 2011)) ,
  (BestScanned y_pre prev_pre 0 (DigitLower (0)) (-1) )
.

Definition next_year_entail_wit_1_split_goal_10 := 
forall (prev_pre: Z) (y_pre: Z) (PreH1 : (1000 <= y_pre)) (PreH2 : (y_pre <= 9999)) (PreH3 : (1000 <= prev_pre)) (PreH4 : (prev_pre <= 2011)) ,
  ((cons ((y_pre ÷ 1000 )) ((cons (((y_pre ÷ 100 ) % ( 10 ) )) ((cons (((y_pre ÷ 10 ) % ( 10 ) )) ((cons ((y_pre % ( 10 ) )) ((@nil Z))))))))) = (YearDigits (y_pre)))
.

Definition next_year_entail_wit_2_1 := 
forall (prev_pre: Z) (y_pre: Z) (best: Z) (pos: Z) (PreH1 : (pos = 0)) (PreH2 : (pos < 4)) (PreH3 : (1000 <= y_pre)) (PreH4 : (y_pre <= 9999)) (PreH5 : (1000 <= prev_pre)) (PreH6 : (prev_pre <= 2011)) (PreH7 : (0 <= pos)) (PreH8 : (pos <= 4)) (PreH9 : ((-1) <= best)) (PreH10 : (best <= 2011)) (PreH11 : (BestScanned y_pre prev_pre pos (DigitLower (pos)) best )) (PreH12 : (0 <= (Znth 0 (YearDigits (y_pre)) 0))) (PreH13 : ((Znth 0 (YearDigits (y_pre)) 0) <= 9)) (PreH14 : (0 <= (Znth 1 (YearDigits (y_pre)) 0))) (PreH15 : ((Znth 1 (YearDigits (y_pre)) 0) <= 9)) (PreH16 : (0 <= (Znth 2 (YearDigits (y_pre)) 0))) (PreH17 : ((Znth 2 (YearDigits (y_pre)) 0) <= 9)) (PreH18 : (0 <= (Znth 3 (YearDigits (y_pre)) 0))) (PreH19 : ((Znth 3 (YearDigits (y_pre)) 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (YearDigits (y_pre)) )
|--
  (EX (digits: (@list Z)) ,
  “ (1000 <= y_pre) ” 
  &&  “ (y_pre <= 9999) ” 
  &&  “ (1000 <= prev_pre) ” 
  &&  “ (prev_pre <= 2011) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < 4) ” 
  &&  “ ((Znth pos (YearDigits (y_pre)) 0) = (Znth pos (YearDigits (y_pre)) 0)) ” 
  &&  “ ((DigitLower (pos)) <= 1) ” 
  &&  “ (1 <= 10) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 2011) ” 
  &&  “ (BestScanned y_pre prev_pre pos 1 best ) ” 
  &&  “ (1 = (DigitLower (pos))) ” 
  &&  “ (digits = (YearDigits (y_pre))) ” 
  &&  “ (0 <= (Znth 0 digits 0)) ” 
  &&  “ ((Znth 0 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 digits 0)) ” 
  &&  “ ((Znth 1 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 digits 0)) ” 
  &&  “ ((Znth 2 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 digits 0)) ” 
  &&  “ ((Znth 3 digits 0) <= 9) ”
  &&  (IntArray.full ( &( "d" ) ) 4 digits ))
  ||
  (EX (digits: (@list Z)) ,
  “ (1000 <= y_pre) ” 
  &&  “ (y_pre <= 9999) ” 
  &&  “ (1000 <= prev_pre) ” 
  &&  “ (prev_pre <= 2011) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < 4) ” 
  &&  “ ((Znth pos (YearDigits (y_pre)) 0) = (Znth pos (YearDigits (y_pre)) 0)) ” 
  &&  “ ((DigitLower (pos)) <= 1) ” 
  &&  “ (1 <= 10) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 2011) ” 
  &&  “ (BestScanned y_pre prev_pre pos 1 best ) ” 
  &&  “ ((DigitLower (pos)) < 1) ” 
  &&  “ (digits = (replace_Znth (pos) ((1 - 1 )) ((YearDigits (y_pre))))) ” 
  &&  “ (0 <= (Znth 0 digits 0)) ” 
  &&  “ ((Znth 0 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 digits 0)) ” 
  &&  “ ((Znth 1 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 digits 0)) ” 
  &&  “ ((Znth 2 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 digits 0)) ” 
  &&  “ ((Znth 3 digits 0) <= 9) ”
  &&  (IntArray.full ( &( "d" ) ) 4 digits ))
.

Definition next_year_entail_wit_2_2 := 
forall (prev_pre: Z) (y_pre: Z) (best: Z) (pos: Z) (PreH1 : (pos <> 0)) (PreH2 : (pos < 4)) (PreH3 : (1000 <= y_pre)) (PreH4 : (y_pre <= 9999)) (PreH5 : (1000 <= prev_pre)) (PreH6 : (prev_pre <= 2011)) (PreH7 : (0 <= pos)) (PreH8 : (pos <= 4)) (PreH9 : ((-1) <= best)) (PreH10 : (best <= 2011)) (PreH11 : (BestScanned y_pre prev_pre pos (DigitLower (pos)) best )) (PreH12 : (0 <= (Znth 0 (YearDigits (y_pre)) 0))) (PreH13 : ((Znth 0 (YearDigits (y_pre)) 0) <= 9)) (PreH14 : (0 <= (Znth 1 (YearDigits (y_pre)) 0))) (PreH15 : ((Znth 1 (YearDigits (y_pre)) 0) <= 9)) (PreH16 : (0 <= (Znth 2 (YearDigits (y_pre)) 0))) (PreH17 : ((Znth 2 (YearDigits (y_pre)) 0) <= 9)) (PreH18 : (0 <= (Znth 3 (YearDigits (y_pre)) 0))) (PreH19 : ((Znth 3 (YearDigits (y_pre)) 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (YearDigits (y_pre)) )
|--
  (EX (digits: (@list Z)) ,
  “ (1000 <= y_pre) ” 
  &&  “ (y_pre <= 9999) ” 
  &&  “ (1000 <= prev_pre) ” 
  &&  “ (prev_pre <= 2011) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < 4) ” 
  &&  “ ((Znth pos (YearDigits (y_pre)) 0) = (Znth pos (YearDigits (y_pre)) 0)) ” 
  &&  “ ((DigitLower (pos)) <= 0) ” 
  &&  “ (0 <= 10) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 2011) ” 
  &&  “ (BestScanned y_pre prev_pre pos 0 best ) ” 
  &&  “ (0 = (DigitLower (pos))) ” 
  &&  “ (digits = (YearDigits (y_pre))) ” 
  &&  “ (0 <= (Znth 0 digits 0)) ” 
  &&  “ ((Znth 0 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 digits 0)) ” 
  &&  “ ((Znth 1 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 digits 0)) ” 
  &&  “ ((Znth 2 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 digits 0)) ” 
  &&  “ ((Znth 3 digits 0) <= 9) ”
  &&  (IntArray.full ( &( "d" ) ) 4 digits ))
  ||
  (EX (digits: (@list Z)) ,
  “ (1000 <= y_pre) ” 
  &&  “ (y_pre <= 9999) ” 
  &&  “ (1000 <= prev_pre) ” 
  &&  “ (prev_pre <= 2011) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < 4) ” 
  &&  “ ((Znth pos (YearDigits (y_pre)) 0) = (Znth pos (YearDigits (y_pre)) 0)) ” 
  &&  “ ((DigitLower (pos)) <= 0) ” 
  &&  “ (0 <= 10) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 2011) ” 
  &&  “ (BestScanned y_pre prev_pre pos 0 best ) ” 
  &&  “ ((DigitLower (pos)) < 0) ” 
  &&  “ (digits = (replace_Znth (pos) ((0 - 1 )) ((YearDigits (y_pre))))) ” 
  &&  “ (0 <= (Znth 0 digits 0)) ” 
  &&  “ ((Znth 0 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 digits 0)) ” 
  &&  “ ((Znth 1 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 digits 0)) ” 
  &&  “ ((Znth 2 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 digits 0)) ” 
  &&  “ ((Znth 3 digits 0) <= 9) ”
  &&  (IntArray.full ( &( "d" ) ) 4 digits ))
.

Definition next_year_entail_wit_3_1 := 
(
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : (v = (DigitLower (pos)))) (PreH20 : (digits_2 = (YearDigits (y_pre)))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits_2)) )
|--
  EX (digits: (@list Z)) ,
  “ (1000 <= y_pre) ” 
  &&  “ (y_pre <= 9999) ” 
  &&  “ (1000 <= prev_pre) ” 
  &&  “ (prev_pre <= 2011) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < 4) ” 
  &&  “ (old = (Znth pos (YearDigits (y_pre)) 0)) ” 
  &&  “ ((DigitLower (pos)) <= (v + 1 )) ” 
  &&  “ ((v + 1 ) <= 10) ” 
  &&  “ ((-1) <= (((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) )) ” 
  &&  “ ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011) ” 
  &&  “ (BestScanned y_pre prev_pre pos (v + 1 ) (((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) ) ” 
  &&  “ ((DigitLower (pos)) < (v + 1 )) ” 
  &&  “ (digits = (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre))))) ” 
  &&  “ (0 <= (Znth 0 digits 0)) ” 
  &&  “ ((Znth 0 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 digits 0)) ” 
  &&  “ ((Znth 1 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 digits 0)) ” 
  &&  “ ((Znth 2 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 digits 0)) ” 
  &&  “ ((Znth 3 digits 0) <= 9) ”
  &&  (IntArray.full ( &( "d" ) ) 4 digits )
) \/
(
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : (v = (DigitLower (pos)))) (PreH20 : (digits_2 = (YearDigits (y_pre)))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  TT && emp 
|--
  “ ((Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0)) ” 
  &&  “ ((Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0)) ” 
  &&  “ ((Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0)) ” 
  &&  “ ((Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0)) ” 
  &&  “ (BestScanned y_pre prev_pre pos (v + 1 ) (((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) ) ” 
  &&  “ ((replace_Znth (pos) (v) (digits_2)) = (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2))) ”
  &&  emp
).

Definition next_year_entail_wit_3_1_split_goal_1 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : (v = (DigitLower (pos)))) (PreH20 : (digits_2 = (YearDigits (y_pre)))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9)
.

Definition next_year_entail_wit_3_1_split_goal_2 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : (v = (DigitLower (pos)))) (PreH20 : (digits_2 = (YearDigits (y_pre)))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0))
.

Definition next_year_entail_wit_3_1_split_goal_3 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : (v = (DigitLower (pos)))) (PreH20 : (digits_2 = (YearDigits (y_pre)))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9)
.

Definition next_year_entail_wit_3_1_split_goal_4 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : (v = (DigitLower (pos)))) (PreH20 : (digits_2 = (YearDigits (y_pre)))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0))
.

Definition next_year_entail_wit_3_1_split_goal_5 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : (v = (DigitLower (pos)))) (PreH20 : (digits_2 = (YearDigits (y_pre)))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9)
.

Definition next_year_entail_wit_3_1_split_goal_6 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : (v = (DigitLower (pos)))) (PreH20 : (digits_2 = (YearDigits (y_pre)))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0))
.

Definition next_year_entail_wit_3_1_split_goal_7 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : (v = (DigitLower (pos)))) (PreH20 : (digits_2 = (YearDigits (y_pre)))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9)
.

Definition next_year_entail_wit_3_1_split_goal_8 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : (v = (DigitLower (pos)))) (PreH20 : (digits_2 = (YearDigits (y_pre)))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0))
.

Definition next_year_entail_wit_3_1_split_goal_9 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : (v = (DigitLower (pos)))) (PreH20 : (digits_2 = (YearDigits (y_pre)))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  (BestScanned y_pre prev_pre pos (v + 1 ) (((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) )
.

Definition next_year_entail_wit_3_1_split_goal_10 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : (v = (DigitLower (pos)))) (PreH20 : (digits_2 = (YearDigits (y_pre)))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  ((replace_Znth (pos) (v) (digits_2)) = (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)))
.

Definition next_year_entail_wit_3_2 := 
(
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : ((DigitLower (pos)) < v)) (PreH20 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits_2)) )
|--
  EX (digits: (@list Z)) ,
  “ (1000 <= y_pre) ” 
  &&  “ (y_pre <= 9999) ” 
  &&  “ (1000 <= prev_pre) ” 
  &&  “ (prev_pre <= 2011) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < 4) ” 
  &&  “ (old = (Znth pos (YearDigits (y_pre)) 0)) ” 
  &&  “ ((DigitLower (pos)) <= (v + 1 )) ” 
  &&  “ ((v + 1 ) <= 10) ” 
  &&  “ ((-1) <= (((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) )) ” 
  &&  “ ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011) ” 
  &&  “ (BestScanned y_pre prev_pre pos (v + 1 ) (((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) ) ” 
  &&  “ ((DigitLower (pos)) < (v + 1 )) ” 
  &&  “ (digits = (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre))))) ” 
  &&  “ (0 <= (Znth 0 digits 0)) ” 
  &&  “ ((Znth 0 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 digits 0)) ” 
  &&  “ ((Znth 1 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 digits 0)) ” 
  &&  “ ((Znth 2 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 digits 0)) ” 
  &&  “ ((Znth 3 digits 0) <= 9) ”
  &&  (IntArray.full ( &( "d" ) ) 4 digits )
) \/
(
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : ((DigitLower (pos)) < v)) (PreH20 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  TT && emp 
|--
  “ ((Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0)) ” 
  &&  “ ((Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0)) ” 
  &&  “ ((Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0)) ” 
  &&  “ ((Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9) ” 
  &&  “ (0 <= (Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0)) ” 
  &&  “ (BestScanned y_pre prev_pre pos (v + 1 ) (((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) ) ” 
  &&  “ ((replace_Znth (pos) (v) (digits_2)) = (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre))))) ”
  &&  emp
).

Definition next_year_entail_wit_3_2_split_goal_1 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : ((DigitLower (pos)) < v)) (PreH20 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9)
.

Definition next_year_entail_wit_3_2_split_goal_2 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : ((DigitLower (pos)) < v)) (PreH20 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0))
.

Definition next_year_entail_wit_3_2_split_goal_3 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : ((DigitLower (pos)) < v)) (PreH20 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9)
.

Definition next_year_entail_wit_3_2_split_goal_4 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : ((DigitLower (pos)) < v)) (PreH20 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0))
.

Definition next_year_entail_wit_3_2_split_goal_5 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : ((DigitLower (pos)) < v)) (PreH20 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9)
.

Definition next_year_entail_wit_3_2_split_goal_6 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : ((DigitLower (pos)) < v)) (PreH20 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0))
.

Definition next_year_entail_wit_3_2_split_goal_7 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : ((DigitLower (pos)) < v)) (PreH20 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9)
.

Definition next_year_entail_wit_3_2_split_goal_8 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : ((DigitLower (pos)) < v)) (PreH20 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0))
.

Definition next_year_entail_wit_3_2_split_goal_9 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : ((DigitLower (pos)) < v)) (PreH20 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  (BestScanned y_pre prev_pre pos (v + 1 ) (((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) )
.

Definition next_year_entail_wit_3_2_split_goal_10 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : ((DigitLower (pos)) < v)) (PreH20 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  ((replace_Znth (pos) (v) (digits_2)) = (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))))
.

Definition next_year_entail_wit_3_3 := 
(
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (best < 0)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH5 : (v <= 9)) (PreH6 : (1000 <= y_pre)) (PreH7 : (y_pre <= 9999)) (PreH8 : (1000 <= prev_pre)) (PreH9 : (prev_pre <= 2011)) (PreH10 : (0 <= pos)) (PreH11 : (pos < 4)) (PreH12 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH13 : ((DigitLower (pos)) <= v)) (PreH14 : (v <= 10)) (PreH15 : ((-1) <= best)) (PreH16 : (best <= 2011)) (PreH17 : (BestScanned y_pre prev_pre pos v best )) (PreH18 : ((DigitLower (pos)) < v)) (PreH19 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH20 : (0 <= (Znth 0 digits_2 0))) (PreH21 : ((Znth 0 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 1 digits_2 0))) (PreH23 : ((Znth 1 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 2 digits_2 0))) (PreH25 : ((Znth 2 digits_2 0) <= 9)) (PreH26 : (0 <= (Znth 3 digits_2 0))) (PreH27 : ((Znth 3 digits_2 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits_2)) )
|--
  EX (digits: (@list Z)) ,
  “ (1000 <= y_pre) ” 
  &&  “ (y_pre <= 9999) ” 
  &&  “ (1000 <= prev_pre) ” 
  &&  “ (prev_pre <= 2011) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < 4) ” 
  &&  “ (old = (Znth pos (YearDigits (y_pre)) 0)) ” 
  &&  “ ((DigitLower (pos)) <= (v + 1 )) ” 
  &&  “ ((v + 1 ) <= 10) ” 
  &&  “ ((-1) <= (((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) )) ” 
  &&  “ ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011) ” 
  &&  “ (BestScanned y_pre prev_pre pos (v + 1 ) (((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) ) ” 
  &&  “ ((DigitLower (pos)) < (v + 1 )) ” 
  &&  “ (digits = (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre))))) ” 
  &&  “ (0 <= (Znth 0 digits 0)) ” 
  &&  “ ((Znth 0 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 digits 0)) ” 
  &&  “ ((Znth 1 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 digits 0)) ” 
  &&  “ ((Znth 2 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 digits 0)) ” 
  &&  “ ((Znth 3 digits 0) <= 9) ”
  &&  (IntArray.full ( &( "d" ) ) 4 digits )
) \/
(
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (best < 0)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH5 : (v <= 9)) (PreH6 : (1000 <= y_pre)) (PreH7 : (y_pre <= 9999)) (PreH8 : (1000 <= prev_pre)) (PreH9 : (prev_pre <= 2011)) (PreH10 : (0 <= pos)) (PreH11 : (pos < 4)) (PreH12 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH13 : ((DigitLower (pos)) <= v)) (PreH14 : (v <= 10)) (PreH15 : ((-1) <= best)) (PreH16 : (best <= 2011)) (PreH17 : (BestScanned y_pre prev_pre pos v best )) (PreH18 : ((DigitLower (pos)) < v)) (PreH19 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH20 : (0 <= (Znth 0 digits_2 0))) (PreH21 : ((Znth 0 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 1 digits_2 0))) (PreH23 : ((Znth 1 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 2 digits_2 0))) (PreH25 : ((Znth 2 digits_2 0) <= 9)) (PreH26 : (0 <= (Znth 3 digits_2 0))) (PreH27 : ((Znth 3 digits_2 0) <= 9)) ,
  TT && emp 
|--
  “ ((Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0)) ” 
  &&  “ ((Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0)) ” 
  &&  “ ((Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0)) ” 
  &&  “ ((Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9) ” 
  &&  “ (0 <= (Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0)) ” 
  &&  “ (BestScanned y_pre prev_pre pos (v + 1 ) (((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) ) ” 
  &&  “ ((replace_Znth (pos) (v) (digits_2)) = (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre))))) ”
  &&  emp
).

Definition next_year_entail_wit_3_3_split_goal_1 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (best < 0)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH5 : (v <= 9)) (PreH6 : (1000 <= y_pre)) (PreH7 : (y_pre <= 9999)) (PreH8 : (1000 <= prev_pre)) (PreH9 : (prev_pre <= 2011)) (PreH10 : (0 <= pos)) (PreH11 : (pos < 4)) (PreH12 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH13 : ((DigitLower (pos)) <= v)) (PreH14 : (v <= 10)) (PreH15 : ((-1) <= best)) (PreH16 : (best <= 2011)) (PreH17 : (BestScanned y_pre prev_pre pos v best )) (PreH18 : ((DigitLower (pos)) < v)) (PreH19 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH20 : (0 <= (Znth 0 digits_2 0))) (PreH21 : ((Znth 0 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 1 digits_2 0))) (PreH23 : ((Znth 1 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 2 digits_2 0))) (PreH25 : ((Znth 2 digits_2 0) <= 9)) (PreH26 : (0 <= (Znth 3 digits_2 0))) (PreH27 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9)
.

Definition next_year_entail_wit_3_3_split_goal_2 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (best < 0)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH5 : (v <= 9)) (PreH6 : (1000 <= y_pre)) (PreH7 : (y_pre <= 9999)) (PreH8 : (1000 <= prev_pre)) (PreH9 : (prev_pre <= 2011)) (PreH10 : (0 <= pos)) (PreH11 : (pos < 4)) (PreH12 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH13 : ((DigitLower (pos)) <= v)) (PreH14 : (v <= 10)) (PreH15 : ((-1) <= best)) (PreH16 : (best <= 2011)) (PreH17 : (BestScanned y_pre prev_pre pos v best )) (PreH18 : ((DigitLower (pos)) < v)) (PreH19 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH20 : (0 <= (Znth 0 digits_2 0))) (PreH21 : ((Znth 0 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 1 digits_2 0))) (PreH23 : ((Znth 1 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 2 digits_2 0))) (PreH25 : ((Znth 2 digits_2 0) <= 9)) (PreH26 : (0 <= (Znth 3 digits_2 0))) (PreH27 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0))
.

Definition next_year_entail_wit_3_3_split_goal_3 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (best < 0)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH5 : (v <= 9)) (PreH6 : (1000 <= y_pre)) (PreH7 : (y_pre <= 9999)) (PreH8 : (1000 <= prev_pre)) (PreH9 : (prev_pre <= 2011)) (PreH10 : (0 <= pos)) (PreH11 : (pos < 4)) (PreH12 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH13 : ((DigitLower (pos)) <= v)) (PreH14 : (v <= 10)) (PreH15 : ((-1) <= best)) (PreH16 : (best <= 2011)) (PreH17 : (BestScanned y_pre prev_pre pos v best )) (PreH18 : ((DigitLower (pos)) < v)) (PreH19 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH20 : (0 <= (Znth 0 digits_2 0))) (PreH21 : ((Znth 0 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 1 digits_2 0))) (PreH23 : ((Znth 1 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 2 digits_2 0))) (PreH25 : ((Znth 2 digits_2 0) <= 9)) (PreH26 : (0 <= (Znth 3 digits_2 0))) (PreH27 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9)
.

Definition next_year_entail_wit_3_3_split_goal_4 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (best < 0)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH5 : (v <= 9)) (PreH6 : (1000 <= y_pre)) (PreH7 : (y_pre <= 9999)) (PreH8 : (1000 <= prev_pre)) (PreH9 : (prev_pre <= 2011)) (PreH10 : (0 <= pos)) (PreH11 : (pos < 4)) (PreH12 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH13 : ((DigitLower (pos)) <= v)) (PreH14 : (v <= 10)) (PreH15 : ((-1) <= best)) (PreH16 : (best <= 2011)) (PreH17 : (BestScanned y_pre prev_pre pos v best )) (PreH18 : ((DigitLower (pos)) < v)) (PreH19 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH20 : (0 <= (Znth 0 digits_2 0))) (PreH21 : ((Znth 0 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 1 digits_2 0))) (PreH23 : ((Znth 1 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 2 digits_2 0))) (PreH25 : ((Znth 2 digits_2 0) <= 9)) (PreH26 : (0 <= (Znth 3 digits_2 0))) (PreH27 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0))
.

Definition next_year_entail_wit_3_3_split_goal_5 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (best < 0)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH5 : (v <= 9)) (PreH6 : (1000 <= y_pre)) (PreH7 : (y_pre <= 9999)) (PreH8 : (1000 <= prev_pre)) (PreH9 : (prev_pre <= 2011)) (PreH10 : (0 <= pos)) (PreH11 : (pos < 4)) (PreH12 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH13 : ((DigitLower (pos)) <= v)) (PreH14 : (v <= 10)) (PreH15 : ((-1) <= best)) (PreH16 : (best <= 2011)) (PreH17 : (BestScanned y_pre prev_pre pos v best )) (PreH18 : ((DigitLower (pos)) < v)) (PreH19 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH20 : (0 <= (Znth 0 digits_2 0))) (PreH21 : ((Znth 0 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 1 digits_2 0))) (PreH23 : ((Znth 1 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 2 digits_2 0))) (PreH25 : ((Znth 2 digits_2 0) <= 9)) (PreH26 : (0 <= (Znth 3 digits_2 0))) (PreH27 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9)
.

Definition next_year_entail_wit_3_3_split_goal_6 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (best < 0)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH5 : (v <= 9)) (PreH6 : (1000 <= y_pre)) (PreH7 : (y_pre <= 9999)) (PreH8 : (1000 <= prev_pre)) (PreH9 : (prev_pre <= 2011)) (PreH10 : (0 <= pos)) (PreH11 : (pos < 4)) (PreH12 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH13 : ((DigitLower (pos)) <= v)) (PreH14 : (v <= 10)) (PreH15 : ((-1) <= best)) (PreH16 : (best <= 2011)) (PreH17 : (BestScanned y_pre prev_pre pos v best )) (PreH18 : ((DigitLower (pos)) < v)) (PreH19 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH20 : (0 <= (Znth 0 digits_2 0))) (PreH21 : ((Znth 0 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 1 digits_2 0))) (PreH23 : ((Znth 1 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 2 digits_2 0))) (PreH25 : ((Znth 2 digits_2 0) <= 9)) (PreH26 : (0 <= (Znth 3 digits_2 0))) (PreH27 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0))
.

Definition next_year_entail_wit_3_3_split_goal_7 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (best < 0)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH5 : (v <= 9)) (PreH6 : (1000 <= y_pre)) (PreH7 : (y_pre <= 9999)) (PreH8 : (1000 <= prev_pre)) (PreH9 : (prev_pre <= 2011)) (PreH10 : (0 <= pos)) (PreH11 : (pos < 4)) (PreH12 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH13 : ((DigitLower (pos)) <= v)) (PreH14 : (v <= 10)) (PreH15 : ((-1) <= best)) (PreH16 : (best <= 2011)) (PreH17 : (BestScanned y_pre prev_pre pos v best )) (PreH18 : ((DigitLower (pos)) < v)) (PreH19 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH20 : (0 <= (Znth 0 digits_2 0))) (PreH21 : ((Znth 0 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 1 digits_2 0))) (PreH23 : ((Znth 1 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 2 digits_2 0))) (PreH25 : ((Znth 2 digits_2 0) <= 9)) (PreH26 : (0 <= (Znth 3 digits_2 0))) (PreH27 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9)
.

Definition next_year_entail_wit_3_3_split_goal_8 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (best < 0)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH5 : (v <= 9)) (PreH6 : (1000 <= y_pre)) (PreH7 : (y_pre <= 9999)) (PreH8 : (1000 <= prev_pre)) (PreH9 : (prev_pre <= 2011)) (PreH10 : (0 <= pos)) (PreH11 : (pos < 4)) (PreH12 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH13 : ((DigitLower (pos)) <= v)) (PreH14 : (v <= 10)) (PreH15 : ((-1) <= best)) (PreH16 : (best <= 2011)) (PreH17 : (BestScanned y_pre prev_pre pos v best )) (PreH18 : ((DigitLower (pos)) < v)) (PreH19 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH20 : (0 <= (Znth 0 digits_2 0))) (PreH21 : ((Znth 0 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 1 digits_2 0))) (PreH23 : ((Znth 1 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 2 digits_2 0))) (PreH25 : ((Znth 2 digits_2 0) <= 9)) (PreH26 : (0 <= (Znth 3 digits_2 0))) (PreH27 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0))
.

Definition next_year_entail_wit_3_3_split_goal_9 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (best < 0)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH5 : (v <= 9)) (PreH6 : (1000 <= y_pre)) (PreH7 : (y_pre <= 9999)) (PreH8 : (1000 <= prev_pre)) (PreH9 : (prev_pre <= 2011)) (PreH10 : (0 <= pos)) (PreH11 : (pos < 4)) (PreH12 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH13 : ((DigitLower (pos)) <= v)) (PreH14 : (v <= 10)) (PreH15 : ((-1) <= best)) (PreH16 : (best <= 2011)) (PreH17 : (BestScanned y_pre prev_pre pos v best )) (PreH18 : ((DigitLower (pos)) < v)) (PreH19 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH20 : (0 <= (Znth 0 digits_2 0))) (PreH21 : ((Znth 0 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 1 digits_2 0))) (PreH23 : ((Znth 1 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 2 digits_2 0))) (PreH25 : ((Znth 2 digits_2 0) <= 9)) (PreH26 : (0 <= (Znth 3 digits_2 0))) (PreH27 : ((Znth 3 digits_2 0) <= 9)) ,
  (BestScanned y_pre prev_pre pos (v + 1 ) (((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) )
.

Definition next_year_entail_wit_3_3_split_goal_10 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (best < 0)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH5 : (v <= 9)) (PreH6 : (1000 <= y_pre)) (PreH7 : (y_pre <= 9999)) (PreH8 : (1000 <= prev_pre)) (PreH9 : (prev_pre <= 2011)) (PreH10 : (0 <= pos)) (PreH11 : (pos < 4)) (PreH12 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH13 : ((DigitLower (pos)) <= v)) (PreH14 : (v <= 10)) (PreH15 : ((-1) <= best)) (PreH16 : (best <= 2011)) (PreH17 : (BestScanned y_pre prev_pre pos v best )) (PreH18 : ((DigitLower (pos)) < v)) (PreH19 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH20 : (0 <= (Znth 0 digits_2 0))) (PreH21 : ((Znth 0 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 1 digits_2 0))) (PreH23 : ((Znth 1 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 2 digits_2 0))) (PreH25 : ((Znth 2 digits_2 0) <= 9)) (PreH26 : (0 <= (Znth 3 digits_2 0))) (PreH27 : ((Znth 3 digits_2 0) <= 9)) ,
  ((replace_Znth (pos) (v) (digits_2)) = (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))))
.

Definition next_year_entail_wit_3_4 := 
(
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (best < 0)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH5 : (v <= 9)) (PreH6 : (1000 <= y_pre)) (PreH7 : (y_pre <= 9999)) (PreH8 : (1000 <= prev_pre)) (PreH9 : (prev_pre <= 2011)) (PreH10 : (0 <= pos)) (PreH11 : (pos < 4)) (PreH12 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH13 : ((DigitLower (pos)) <= v)) (PreH14 : (v <= 10)) (PreH15 : ((-1) <= best)) (PreH16 : (best <= 2011)) (PreH17 : (BestScanned y_pre prev_pre pos v best )) (PreH18 : (v = (DigitLower (pos)))) (PreH19 : (digits_2 = (YearDigits (y_pre)))) (PreH20 : (0 <= (Znth 0 digits_2 0))) (PreH21 : ((Znth 0 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 1 digits_2 0))) (PreH23 : ((Znth 1 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 2 digits_2 0))) (PreH25 : ((Znth 2 digits_2 0) <= 9)) (PreH26 : (0 <= (Znth 3 digits_2 0))) (PreH27 : ((Znth 3 digits_2 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits_2)) )
|--
  EX (digits: (@list Z)) ,
  “ (1000 <= y_pre) ” 
  &&  “ (y_pre <= 9999) ” 
  &&  “ (1000 <= prev_pre) ” 
  &&  “ (prev_pre <= 2011) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < 4) ” 
  &&  “ (old = (Znth pos (YearDigits (y_pre)) 0)) ” 
  &&  “ ((DigitLower (pos)) <= (v + 1 )) ” 
  &&  “ ((v + 1 ) <= 10) ” 
  &&  “ ((-1) <= (((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) )) ” 
  &&  “ ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011) ” 
  &&  “ (BestScanned y_pre prev_pre pos (v + 1 ) (((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) ) ” 
  &&  “ ((DigitLower (pos)) < (v + 1 )) ” 
  &&  “ (digits = (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre))))) ” 
  &&  “ (0 <= (Znth 0 digits 0)) ” 
  &&  “ ((Znth 0 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 digits 0)) ” 
  &&  “ ((Znth 1 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 digits 0)) ” 
  &&  “ ((Znth 2 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 digits 0)) ” 
  &&  “ ((Znth 3 digits 0) <= 9) ”
  &&  (IntArray.full ( &( "d" ) ) 4 digits )
) \/
(
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (best < 0)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH5 : (v <= 9)) (PreH6 : (1000 <= y_pre)) (PreH7 : (y_pre <= 9999)) (PreH8 : (1000 <= prev_pre)) (PreH9 : (prev_pre <= 2011)) (PreH10 : (0 <= pos)) (PreH11 : (pos < 4)) (PreH12 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH13 : ((DigitLower (pos)) <= v)) (PreH14 : (v <= 10)) (PreH15 : ((-1) <= best)) (PreH16 : (best <= 2011)) (PreH17 : (BestScanned y_pre prev_pre pos v best )) (PreH18 : (v = (DigitLower (pos)))) (PreH19 : (digits_2 = (YearDigits (y_pre)))) (PreH20 : (0 <= (Znth 0 digits_2 0))) (PreH21 : ((Znth 0 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 1 digits_2 0))) (PreH23 : ((Znth 1 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 2 digits_2 0))) (PreH25 : ((Znth 2 digits_2 0) <= 9)) (PreH26 : (0 <= (Znth 3 digits_2 0))) (PreH27 : ((Znth 3 digits_2 0) <= 9)) ,
  TT && emp 
|--
  “ ((Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0)) ” 
  &&  “ ((Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0)) ” 
  &&  “ ((Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0)) ” 
  &&  “ ((Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0)) ” 
  &&  “ (BestScanned y_pre prev_pre pos (v + 1 ) (((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) ) ” 
  &&  “ ((replace_Znth (pos) (v) (digits_2)) = (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2))) ”
  &&  emp
).

Definition next_year_entail_wit_3_4_split_goal_1 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (best < 0)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH5 : (v <= 9)) (PreH6 : (1000 <= y_pre)) (PreH7 : (y_pre <= 9999)) (PreH8 : (1000 <= prev_pre)) (PreH9 : (prev_pre <= 2011)) (PreH10 : (0 <= pos)) (PreH11 : (pos < 4)) (PreH12 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH13 : ((DigitLower (pos)) <= v)) (PreH14 : (v <= 10)) (PreH15 : ((-1) <= best)) (PreH16 : (best <= 2011)) (PreH17 : (BestScanned y_pre prev_pre pos v best )) (PreH18 : (v = (DigitLower (pos)))) (PreH19 : (digits_2 = (YearDigits (y_pre)))) (PreH20 : (0 <= (Znth 0 digits_2 0))) (PreH21 : ((Znth 0 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 1 digits_2 0))) (PreH23 : ((Znth 1 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 2 digits_2 0))) (PreH25 : ((Znth 2 digits_2 0) <= 9)) (PreH26 : (0 <= (Znth 3 digits_2 0))) (PreH27 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9)
.

Definition next_year_entail_wit_3_4_split_goal_2 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (best < 0)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH5 : (v <= 9)) (PreH6 : (1000 <= y_pre)) (PreH7 : (y_pre <= 9999)) (PreH8 : (1000 <= prev_pre)) (PreH9 : (prev_pre <= 2011)) (PreH10 : (0 <= pos)) (PreH11 : (pos < 4)) (PreH12 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH13 : ((DigitLower (pos)) <= v)) (PreH14 : (v <= 10)) (PreH15 : ((-1) <= best)) (PreH16 : (best <= 2011)) (PreH17 : (BestScanned y_pre prev_pre pos v best )) (PreH18 : (v = (DigitLower (pos)))) (PreH19 : (digits_2 = (YearDigits (y_pre)))) (PreH20 : (0 <= (Znth 0 digits_2 0))) (PreH21 : ((Znth 0 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 1 digits_2 0))) (PreH23 : ((Znth 1 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 2 digits_2 0))) (PreH25 : ((Znth 2 digits_2 0) <= 9)) (PreH26 : (0 <= (Znth 3 digits_2 0))) (PreH27 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0))
.

Definition next_year_entail_wit_3_4_split_goal_3 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (best < 0)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH5 : (v <= 9)) (PreH6 : (1000 <= y_pre)) (PreH7 : (y_pre <= 9999)) (PreH8 : (1000 <= prev_pre)) (PreH9 : (prev_pre <= 2011)) (PreH10 : (0 <= pos)) (PreH11 : (pos < 4)) (PreH12 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH13 : ((DigitLower (pos)) <= v)) (PreH14 : (v <= 10)) (PreH15 : ((-1) <= best)) (PreH16 : (best <= 2011)) (PreH17 : (BestScanned y_pre prev_pre pos v best )) (PreH18 : (v = (DigitLower (pos)))) (PreH19 : (digits_2 = (YearDigits (y_pre)))) (PreH20 : (0 <= (Znth 0 digits_2 0))) (PreH21 : ((Znth 0 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 1 digits_2 0))) (PreH23 : ((Znth 1 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 2 digits_2 0))) (PreH25 : ((Znth 2 digits_2 0) <= 9)) (PreH26 : (0 <= (Znth 3 digits_2 0))) (PreH27 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9)
.

Definition next_year_entail_wit_3_4_split_goal_4 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (best < 0)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH5 : (v <= 9)) (PreH6 : (1000 <= y_pre)) (PreH7 : (y_pre <= 9999)) (PreH8 : (1000 <= prev_pre)) (PreH9 : (prev_pre <= 2011)) (PreH10 : (0 <= pos)) (PreH11 : (pos < 4)) (PreH12 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH13 : ((DigitLower (pos)) <= v)) (PreH14 : (v <= 10)) (PreH15 : ((-1) <= best)) (PreH16 : (best <= 2011)) (PreH17 : (BestScanned y_pre prev_pre pos v best )) (PreH18 : (v = (DigitLower (pos)))) (PreH19 : (digits_2 = (YearDigits (y_pre)))) (PreH20 : (0 <= (Znth 0 digits_2 0))) (PreH21 : ((Znth 0 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 1 digits_2 0))) (PreH23 : ((Znth 1 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 2 digits_2 0))) (PreH25 : ((Znth 2 digits_2 0) <= 9)) (PreH26 : (0 <= (Znth 3 digits_2 0))) (PreH27 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0))
.

Definition next_year_entail_wit_3_4_split_goal_5 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (best < 0)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH5 : (v <= 9)) (PreH6 : (1000 <= y_pre)) (PreH7 : (y_pre <= 9999)) (PreH8 : (1000 <= prev_pre)) (PreH9 : (prev_pre <= 2011)) (PreH10 : (0 <= pos)) (PreH11 : (pos < 4)) (PreH12 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH13 : ((DigitLower (pos)) <= v)) (PreH14 : (v <= 10)) (PreH15 : ((-1) <= best)) (PreH16 : (best <= 2011)) (PreH17 : (BestScanned y_pre prev_pre pos v best )) (PreH18 : (v = (DigitLower (pos)))) (PreH19 : (digits_2 = (YearDigits (y_pre)))) (PreH20 : (0 <= (Znth 0 digits_2 0))) (PreH21 : ((Znth 0 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 1 digits_2 0))) (PreH23 : ((Znth 1 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 2 digits_2 0))) (PreH25 : ((Znth 2 digits_2 0) <= 9)) (PreH26 : (0 <= (Znth 3 digits_2 0))) (PreH27 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9)
.

Definition next_year_entail_wit_3_4_split_goal_6 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (best < 0)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH5 : (v <= 9)) (PreH6 : (1000 <= y_pre)) (PreH7 : (y_pre <= 9999)) (PreH8 : (1000 <= prev_pre)) (PreH9 : (prev_pre <= 2011)) (PreH10 : (0 <= pos)) (PreH11 : (pos < 4)) (PreH12 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH13 : ((DigitLower (pos)) <= v)) (PreH14 : (v <= 10)) (PreH15 : ((-1) <= best)) (PreH16 : (best <= 2011)) (PreH17 : (BestScanned y_pre prev_pre pos v best )) (PreH18 : (v = (DigitLower (pos)))) (PreH19 : (digits_2 = (YearDigits (y_pre)))) (PreH20 : (0 <= (Znth 0 digits_2 0))) (PreH21 : ((Znth 0 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 1 digits_2 0))) (PreH23 : ((Znth 1 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 2 digits_2 0))) (PreH25 : ((Znth 2 digits_2 0) <= 9)) (PreH26 : (0 <= (Znth 3 digits_2 0))) (PreH27 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0))
.

Definition next_year_entail_wit_3_4_split_goal_7 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (best < 0)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH5 : (v <= 9)) (PreH6 : (1000 <= y_pre)) (PreH7 : (y_pre <= 9999)) (PreH8 : (1000 <= prev_pre)) (PreH9 : (prev_pre <= 2011)) (PreH10 : (0 <= pos)) (PreH11 : (pos < 4)) (PreH12 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH13 : ((DigitLower (pos)) <= v)) (PreH14 : (v <= 10)) (PreH15 : ((-1) <= best)) (PreH16 : (best <= 2011)) (PreH17 : (BestScanned y_pre prev_pre pos v best )) (PreH18 : (v = (DigitLower (pos)))) (PreH19 : (digits_2 = (YearDigits (y_pre)))) (PreH20 : (0 <= (Znth 0 digits_2 0))) (PreH21 : ((Znth 0 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 1 digits_2 0))) (PreH23 : ((Znth 1 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 2 digits_2 0))) (PreH25 : ((Znth 2 digits_2 0) <= 9)) (PreH26 : (0 <= (Znth 3 digits_2 0))) (PreH27 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9)
.

Definition next_year_entail_wit_3_4_split_goal_8 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (best < 0)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH5 : (v <= 9)) (PreH6 : (1000 <= y_pre)) (PreH7 : (y_pre <= 9999)) (PreH8 : (1000 <= prev_pre)) (PreH9 : (prev_pre <= 2011)) (PreH10 : (0 <= pos)) (PreH11 : (pos < 4)) (PreH12 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH13 : ((DigitLower (pos)) <= v)) (PreH14 : (v <= 10)) (PreH15 : ((-1) <= best)) (PreH16 : (best <= 2011)) (PreH17 : (BestScanned y_pre prev_pre pos v best )) (PreH18 : (v = (DigitLower (pos)))) (PreH19 : (digits_2 = (YearDigits (y_pre)))) (PreH20 : (0 <= (Znth 0 digits_2 0))) (PreH21 : ((Znth 0 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 1 digits_2 0))) (PreH23 : ((Znth 1 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 2 digits_2 0))) (PreH25 : ((Znth 2 digits_2 0) <= 9)) (PreH26 : (0 <= (Znth 3 digits_2 0))) (PreH27 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0))
.

Definition next_year_entail_wit_3_4_split_goal_9 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (best < 0)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH5 : (v <= 9)) (PreH6 : (1000 <= y_pre)) (PreH7 : (y_pre <= 9999)) (PreH8 : (1000 <= prev_pre)) (PreH9 : (prev_pre <= 2011)) (PreH10 : (0 <= pos)) (PreH11 : (pos < 4)) (PreH12 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH13 : ((DigitLower (pos)) <= v)) (PreH14 : (v <= 10)) (PreH15 : ((-1) <= best)) (PreH16 : (best <= 2011)) (PreH17 : (BestScanned y_pre prev_pre pos v best )) (PreH18 : (v = (DigitLower (pos)))) (PreH19 : (digits_2 = (YearDigits (y_pre)))) (PreH20 : (0 <= (Znth 0 digits_2 0))) (PreH21 : ((Znth 0 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 1 digits_2 0))) (PreH23 : ((Znth 1 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 2 digits_2 0))) (PreH25 : ((Znth 2 digits_2 0) <= 9)) (PreH26 : (0 <= (Znth 3 digits_2 0))) (PreH27 : ((Znth 3 digits_2 0) <= 9)) ,
  (BestScanned y_pre prev_pre pos (v + 1 ) (((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) )
.

Definition next_year_entail_wit_3_4_split_goal_10 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (best < 0)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH5 : (v <= 9)) (PreH6 : (1000 <= y_pre)) (PreH7 : (y_pre <= 9999)) (PreH8 : (1000 <= prev_pre)) (PreH9 : (prev_pre <= 2011)) (PreH10 : (0 <= pos)) (PreH11 : (pos < 4)) (PreH12 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH13 : ((DigitLower (pos)) <= v)) (PreH14 : (v <= 10)) (PreH15 : ((-1) <= best)) (PreH16 : (best <= 2011)) (PreH17 : (BestScanned y_pre prev_pre pos v best )) (PreH18 : (v = (DigitLower (pos)))) (PreH19 : (digits_2 = (YearDigits (y_pre)))) (PreH20 : (0 <= (Znth 0 digits_2 0))) (PreH21 : ((Znth 0 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 1 digits_2 0))) (PreH23 : ((Znth 1 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 2 digits_2 0))) (PreH25 : ((Znth 2 digits_2 0) <= 9)) (PreH26 : (0 <= (Znth 3 digits_2 0))) (PreH27 : ((Znth 3 digits_2 0) <= 9)) ,
  ((replace_Znth (pos) (v) (digits_2)) = (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)))
.

Definition next_year_entail_wit_3_5 := 
(
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < prev_pre)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH4 : (v <= 9)) (PreH5 : (1000 <= y_pre)) (PreH6 : (y_pre <= 9999)) (PreH7 : (1000 <= prev_pre)) (PreH8 : (prev_pre <= 2011)) (PreH9 : (0 <= pos)) (PreH10 : (pos < 4)) (PreH11 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH12 : ((DigitLower (pos)) <= v)) (PreH13 : (v <= 10)) (PreH14 : ((-1) <= best)) (PreH15 : (best <= 2011)) (PreH16 : (BestScanned y_pre prev_pre pos v best )) (PreH17 : ((DigitLower (pos)) < v)) (PreH18 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH19 : (0 <= (Znth 0 digits_2 0))) (PreH20 : ((Znth 0 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 1 digits_2 0))) (PreH22 : ((Znth 1 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 2 digits_2 0))) (PreH24 : ((Znth 2 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 3 digits_2 0))) (PreH26 : ((Znth 3 digits_2 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits_2)) )
|--
  EX (digits: (@list Z)) ,
  “ (1000 <= y_pre) ” 
  &&  “ (y_pre <= 9999) ” 
  &&  “ (1000 <= prev_pre) ” 
  &&  “ (prev_pre <= 2011) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < 4) ” 
  &&  “ (old = (Znth pos (YearDigits (y_pre)) 0)) ” 
  &&  “ ((DigitLower (pos)) <= (v + 1 )) ” 
  &&  “ ((v + 1 ) <= 10) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 2011) ” 
  &&  “ (BestScanned y_pre prev_pre pos (v + 1 ) best ) ” 
  &&  “ ((DigitLower (pos)) < (v + 1 )) ” 
  &&  “ (digits = (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre))))) ” 
  &&  “ (0 <= (Znth 0 digits 0)) ” 
  &&  “ ((Znth 0 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 digits 0)) ” 
  &&  “ ((Znth 1 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 digits 0)) ” 
  &&  “ ((Znth 2 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 digits 0)) ” 
  &&  “ ((Znth 3 digits 0) <= 9) ”
  &&  (IntArray.full ( &( "d" ) ) 4 digits )
) \/
(
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < prev_pre)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH4 : (v <= 9)) (PreH5 : (1000 <= y_pre)) (PreH6 : (y_pre <= 9999)) (PreH7 : (1000 <= prev_pre)) (PreH8 : (prev_pre <= 2011)) (PreH9 : (0 <= pos)) (PreH10 : (pos < 4)) (PreH11 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH12 : ((DigitLower (pos)) <= v)) (PreH13 : (v <= 10)) (PreH14 : ((-1) <= best)) (PreH15 : (best <= 2011)) (PreH16 : (BestScanned y_pre prev_pre pos v best )) (PreH17 : ((DigitLower (pos)) < v)) (PreH18 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH19 : (0 <= (Znth 0 digits_2 0))) (PreH20 : ((Znth 0 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 1 digits_2 0))) (PreH22 : ((Znth 1 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 2 digits_2 0))) (PreH24 : ((Znth 2 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 3 digits_2 0))) (PreH26 : ((Znth 3 digits_2 0) <= 9)) ,
  TT && emp 
|--
  “ ((Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0)) ” 
  &&  “ ((Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0)) ” 
  &&  “ ((Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0)) ” 
  &&  “ ((Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9) ” 
  &&  “ (0 <= (Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0)) ” 
  &&  “ (BestScanned y_pre prev_pre pos (v + 1 ) best ) ” 
  &&  “ ((replace_Znth (pos) (v) (digits_2)) = (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre))))) ”
  &&  emp
).

Definition next_year_entail_wit_3_5_split_goal_1 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < prev_pre)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH4 : (v <= 9)) (PreH5 : (1000 <= y_pre)) (PreH6 : (y_pre <= 9999)) (PreH7 : (1000 <= prev_pre)) (PreH8 : (prev_pre <= 2011)) (PreH9 : (0 <= pos)) (PreH10 : (pos < 4)) (PreH11 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH12 : ((DigitLower (pos)) <= v)) (PreH13 : (v <= 10)) (PreH14 : ((-1) <= best)) (PreH15 : (best <= 2011)) (PreH16 : (BestScanned y_pre prev_pre pos v best )) (PreH17 : ((DigitLower (pos)) < v)) (PreH18 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH19 : (0 <= (Znth 0 digits_2 0))) (PreH20 : ((Znth 0 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 1 digits_2 0))) (PreH22 : ((Znth 1 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 2 digits_2 0))) (PreH24 : ((Znth 2 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 3 digits_2 0))) (PreH26 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9)
.

Definition next_year_entail_wit_3_5_split_goal_2 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < prev_pre)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH4 : (v <= 9)) (PreH5 : (1000 <= y_pre)) (PreH6 : (y_pre <= 9999)) (PreH7 : (1000 <= prev_pre)) (PreH8 : (prev_pre <= 2011)) (PreH9 : (0 <= pos)) (PreH10 : (pos < 4)) (PreH11 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH12 : ((DigitLower (pos)) <= v)) (PreH13 : (v <= 10)) (PreH14 : ((-1) <= best)) (PreH15 : (best <= 2011)) (PreH16 : (BestScanned y_pre prev_pre pos v best )) (PreH17 : ((DigitLower (pos)) < v)) (PreH18 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH19 : (0 <= (Znth 0 digits_2 0))) (PreH20 : ((Znth 0 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 1 digits_2 0))) (PreH22 : ((Znth 1 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 2 digits_2 0))) (PreH24 : ((Znth 2 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 3 digits_2 0))) (PreH26 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0))
.

Definition next_year_entail_wit_3_5_split_goal_3 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < prev_pre)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH4 : (v <= 9)) (PreH5 : (1000 <= y_pre)) (PreH6 : (y_pre <= 9999)) (PreH7 : (1000 <= prev_pre)) (PreH8 : (prev_pre <= 2011)) (PreH9 : (0 <= pos)) (PreH10 : (pos < 4)) (PreH11 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH12 : ((DigitLower (pos)) <= v)) (PreH13 : (v <= 10)) (PreH14 : ((-1) <= best)) (PreH15 : (best <= 2011)) (PreH16 : (BestScanned y_pre prev_pre pos v best )) (PreH17 : ((DigitLower (pos)) < v)) (PreH18 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH19 : (0 <= (Znth 0 digits_2 0))) (PreH20 : ((Znth 0 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 1 digits_2 0))) (PreH22 : ((Znth 1 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 2 digits_2 0))) (PreH24 : ((Znth 2 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 3 digits_2 0))) (PreH26 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9)
.

Definition next_year_entail_wit_3_5_split_goal_4 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < prev_pre)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH4 : (v <= 9)) (PreH5 : (1000 <= y_pre)) (PreH6 : (y_pre <= 9999)) (PreH7 : (1000 <= prev_pre)) (PreH8 : (prev_pre <= 2011)) (PreH9 : (0 <= pos)) (PreH10 : (pos < 4)) (PreH11 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH12 : ((DigitLower (pos)) <= v)) (PreH13 : (v <= 10)) (PreH14 : ((-1) <= best)) (PreH15 : (best <= 2011)) (PreH16 : (BestScanned y_pre prev_pre pos v best )) (PreH17 : ((DigitLower (pos)) < v)) (PreH18 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH19 : (0 <= (Znth 0 digits_2 0))) (PreH20 : ((Znth 0 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 1 digits_2 0))) (PreH22 : ((Znth 1 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 2 digits_2 0))) (PreH24 : ((Znth 2 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 3 digits_2 0))) (PreH26 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0))
.

Definition next_year_entail_wit_3_5_split_goal_5 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < prev_pre)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH4 : (v <= 9)) (PreH5 : (1000 <= y_pre)) (PreH6 : (y_pre <= 9999)) (PreH7 : (1000 <= prev_pre)) (PreH8 : (prev_pre <= 2011)) (PreH9 : (0 <= pos)) (PreH10 : (pos < 4)) (PreH11 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH12 : ((DigitLower (pos)) <= v)) (PreH13 : (v <= 10)) (PreH14 : ((-1) <= best)) (PreH15 : (best <= 2011)) (PreH16 : (BestScanned y_pre prev_pre pos v best )) (PreH17 : ((DigitLower (pos)) < v)) (PreH18 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH19 : (0 <= (Znth 0 digits_2 0))) (PreH20 : ((Znth 0 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 1 digits_2 0))) (PreH22 : ((Znth 1 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 2 digits_2 0))) (PreH24 : ((Znth 2 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 3 digits_2 0))) (PreH26 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9)
.

Definition next_year_entail_wit_3_5_split_goal_6 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < prev_pre)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH4 : (v <= 9)) (PreH5 : (1000 <= y_pre)) (PreH6 : (y_pre <= 9999)) (PreH7 : (1000 <= prev_pre)) (PreH8 : (prev_pre <= 2011)) (PreH9 : (0 <= pos)) (PreH10 : (pos < 4)) (PreH11 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH12 : ((DigitLower (pos)) <= v)) (PreH13 : (v <= 10)) (PreH14 : ((-1) <= best)) (PreH15 : (best <= 2011)) (PreH16 : (BestScanned y_pre prev_pre pos v best )) (PreH17 : ((DigitLower (pos)) < v)) (PreH18 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH19 : (0 <= (Znth 0 digits_2 0))) (PreH20 : ((Znth 0 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 1 digits_2 0))) (PreH22 : ((Znth 1 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 2 digits_2 0))) (PreH24 : ((Znth 2 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 3 digits_2 0))) (PreH26 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0))
.

Definition next_year_entail_wit_3_5_split_goal_7 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < prev_pre)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH4 : (v <= 9)) (PreH5 : (1000 <= y_pre)) (PreH6 : (y_pre <= 9999)) (PreH7 : (1000 <= prev_pre)) (PreH8 : (prev_pre <= 2011)) (PreH9 : (0 <= pos)) (PreH10 : (pos < 4)) (PreH11 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH12 : ((DigitLower (pos)) <= v)) (PreH13 : (v <= 10)) (PreH14 : ((-1) <= best)) (PreH15 : (best <= 2011)) (PreH16 : (BestScanned y_pre prev_pre pos v best )) (PreH17 : ((DigitLower (pos)) < v)) (PreH18 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH19 : (0 <= (Znth 0 digits_2 0))) (PreH20 : ((Znth 0 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 1 digits_2 0))) (PreH22 : ((Znth 1 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 2 digits_2 0))) (PreH24 : ((Znth 2 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 3 digits_2 0))) (PreH26 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9)
.

Definition next_year_entail_wit_3_5_split_goal_8 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < prev_pre)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH4 : (v <= 9)) (PreH5 : (1000 <= y_pre)) (PreH6 : (y_pre <= 9999)) (PreH7 : (1000 <= prev_pre)) (PreH8 : (prev_pre <= 2011)) (PreH9 : (0 <= pos)) (PreH10 : (pos < 4)) (PreH11 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH12 : ((DigitLower (pos)) <= v)) (PreH13 : (v <= 10)) (PreH14 : ((-1) <= best)) (PreH15 : (best <= 2011)) (PreH16 : (BestScanned y_pre prev_pre pos v best )) (PreH17 : ((DigitLower (pos)) < v)) (PreH18 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH19 : (0 <= (Znth 0 digits_2 0))) (PreH20 : ((Znth 0 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 1 digits_2 0))) (PreH22 : ((Znth 1 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 2 digits_2 0))) (PreH24 : ((Znth 2 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 3 digits_2 0))) (PreH26 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0))
.

Definition next_year_entail_wit_3_5_split_goal_9 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < prev_pre)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH4 : (v <= 9)) (PreH5 : (1000 <= y_pre)) (PreH6 : (y_pre <= 9999)) (PreH7 : (1000 <= prev_pre)) (PreH8 : (prev_pre <= 2011)) (PreH9 : (0 <= pos)) (PreH10 : (pos < 4)) (PreH11 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH12 : ((DigitLower (pos)) <= v)) (PreH13 : (v <= 10)) (PreH14 : ((-1) <= best)) (PreH15 : (best <= 2011)) (PreH16 : (BestScanned y_pre prev_pre pos v best )) (PreH17 : ((DigitLower (pos)) < v)) (PreH18 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH19 : (0 <= (Znth 0 digits_2 0))) (PreH20 : ((Znth 0 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 1 digits_2 0))) (PreH22 : ((Znth 1 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 2 digits_2 0))) (PreH24 : ((Znth 2 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 3 digits_2 0))) (PreH26 : ((Znth 3 digits_2 0) <= 9)) ,
  (BestScanned y_pre prev_pre pos (v + 1 ) best )
.

Definition next_year_entail_wit_3_5_split_goal_10 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < prev_pre)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH4 : (v <= 9)) (PreH5 : (1000 <= y_pre)) (PreH6 : (y_pre <= 9999)) (PreH7 : (1000 <= prev_pre)) (PreH8 : (prev_pre <= 2011)) (PreH9 : (0 <= pos)) (PreH10 : (pos < 4)) (PreH11 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH12 : ((DigitLower (pos)) <= v)) (PreH13 : (v <= 10)) (PreH14 : ((-1) <= best)) (PreH15 : (best <= 2011)) (PreH16 : (BestScanned y_pre prev_pre pos v best )) (PreH17 : ((DigitLower (pos)) < v)) (PreH18 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH19 : (0 <= (Znth 0 digits_2 0))) (PreH20 : ((Znth 0 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 1 digits_2 0))) (PreH22 : ((Znth 1 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 2 digits_2 0))) (PreH24 : ((Znth 2 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 3 digits_2 0))) (PreH26 : ((Znth 3 digits_2 0) <= 9)) ,
  ((replace_Znth (pos) (v) (digits_2)) = (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))))
.

Definition next_year_entail_wit_3_6 := 
(
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < prev_pre)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH4 : (v <= 9)) (PreH5 : (1000 <= y_pre)) (PreH6 : (y_pre <= 9999)) (PreH7 : (1000 <= prev_pre)) (PreH8 : (prev_pre <= 2011)) (PreH9 : (0 <= pos)) (PreH10 : (pos < 4)) (PreH11 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH12 : ((DigitLower (pos)) <= v)) (PreH13 : (v <= 10)) (PreH14 : ((-1) <= best)) (PreH15 : (best <= 2011)) (PreH16 : (BestScanned y_pre prev_pre pos v best )) (PreH17 : (v = (DigitLower (pos)))) (PreH18 : (digits_2 = (YearDigits (y_pre)))) (PreH19 : (0 <= (Znth 0 digits_2 0))) (PreH20 : ((Znth 0 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 1 digits_2 0))) (PreH22 : ((Znth 1 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 2 digits_2 0))) (PreH24 : ((Znth 2 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 3 digits_2 0))) (PreH26 : ((Znth 3 digits_2 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits_2)) )
|--
  EX (digits: (@list Z)) ,
  “ (1000 <= y_pre) ” 
  &&  “ (y_pre <= 9999) ” 
  &&  “ (1000 <= prev_pre) ” 
  &&  “ (prev_pre <= 2011) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < 4) ” 
  &&  “ (old = (Znth pos (YearDigits (y_pre)) 0)) ” 
  &&  “ ((DigitLower (pos)) <= (v + 1 )) ” 
  &&  “ ((v + 1 ) <= 10) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 2011) ” 
  &&  “ (BestScanned y_pre prev_pre pos (v + 1 ) best ) ” 
  &&  “ ((DigitLower (pos)) < (v + 1 )) ” 
  &&  “ (digits = (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre))))) ” 
  &&  “ (0 <= (Znth 0 digits 0)) ” 
  &&  “ ((Znth 0 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 digits 0)) ” 
  &&  “ ((Znth 1 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 digits 0)) ” 
  &&  “ ((Znth 2 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 digits 0)) ” 
  &&  “ ((Znth 3 digits 0) <= 9) ”
  &&  (IntArray.full ( &( "d" ) ) 4 digits )
) \/
(
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < prev_pre)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH4 : (v <= 9)) (PreH5 : (1000 <= y_pre)) (PreH6 : (y_pre <= 9999)) (PreH7 : (1000 <= prev_pre)) (PreH8 : (prev_pre <= 2011)) (PreH9 : (0 <= pos)) (PreH10 : (pos < 4)) (PreH11 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH12 : ((DigitLower (pos)) <= v)) (PreH13 : (v <= 10)) (PreH14 : ((-1) <= best)) (PreH15 : (best <= 2011)) (PreH16 : (BestScanned y_pre prev_pre pos v best )) (PreH17 : (v = (DigitLower (pos)))) (PreH18 : (digits_2 = (YearDigits (y_pre)))) (PreH19 : (0 <= (Znth 0 digits_2 0))) (PreH20 : ((Znth 0 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 1 digits_2 0))) (PreH22 : ((Znth 1 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 2 digits_2 0))) (PreH24 : ((Znth 2 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 3 digits_2 0))) (PreH26 : ((Znth 3 digits_2 0) <= 9)) ,
  TT && emp 
|--
  “ ((Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0)) ” 
  &&  “ ((Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0)) ” 
  &&  “ ((Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0)) ” 
  &&  “ ((Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0)) ” 
  &&  “ (BestScanned y_pre prev_pre pos (v + 1 ) best ) ” 
  &&  “ ((replace_Znth (pos) (v) (digits_2)) = (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2))) ”
  &&  emp
).

Definition next_year_entail_wit_3_6_split_goal_1 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < prev_pre)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH4 : (v <= 9)) (PreH5 : (1000 <= y_pre)) (PreH6 : (y_pre <= 9999)) (PreH7 : (1000 <= prev_pre)) (PreH8 : (prev_pre <= 2011)) (PreH9 : (0 <= pos)) (PreH10 : (pos < 4)) (PreH11 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH12 : ((DigitLower (pos)) <= v)) (PreH13 : (v <= 10)) (PreH14 : ((-1) <= best)) (PreH15 : (best <= 2011)) (PreH16 : (BestScanned y_pre prev_pre pos v best )) (PreH17 : (v = (DigitLower (pos)))) (PreH18 : (digits_2 = (YearDigits (y_pre)))) (PreH19 : (0 <= (Znth 0 digits_2 0))) (PreH20 : ((Znth 0 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 1 digits_2 0))) (PreH22 : ((Znth 1 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 2 digits_2 0))) (PreH24 : ((Znth 2 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 3 digits_2 0))) (PreH26 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9)
.

Definition next_year_entail_wit_3_6_split_goal_2 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < prev_pre)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH4 : (v <= 9)) (PreH5 : (1000 <= y_pre)) (PreH6 : (y_pre <= 9999)) (PreH7 : (1000 <= prev_pre)) (PreH8 : (prev_pre <= 2011)) (PreH9 : (0 <= pos)) (PreH10 : (pos < 4)) (PreH11 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH12 : ((DigitLower (pos)) <= v)) (PreH13 : (v <= 10)) (PreH14 : ((-1) <= best)) (PreH15 : (best <= 2011)) (PreH16 : (BestScanned y_pre prev_pre pos v best )) (PreH17 : (v = (DigitLower (pos)))) (PreH18 : (digits_2 = (YearDigits (y_pre)))) (PreH19 : (0 <= (Znth 0 digits_2 0))) (PreH20 : ((Znth 0 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 1 digits_2 0))) (PreH22 : ((Znth 1 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 2 digits_2 0))) (PreH24 : ((Znth 2 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 3 digits_2 0))) (PreH26 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0))
.

Definition next_year_entail_wit_3_6_split_goal_3 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < prev_pre)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH4 : (v <= 9)) (PreH5 : (1000 <= y_pre)) (PreH6 : (y_pre <= 9999)) (PreH7 : (1000 <= prev_pre)) (PreH8 : (prev_pre <= 2011)) (PreH9 : (0 <= pos)) (PreH10 : (pos < 4)) (PreH11 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH12 : ((DigitLower (pos)) <= v)) (PreH13 : (v <= 10)) (PreH14 : ((-1) <= best)) (PreH15 : (best <= 2011)) (PreH16 : (BestScanned y_pre prev_pre pos v best )) (PreH17 : (v = (DigitLower (pos)))) (PreH18 : (digits_2 = (YearDigits (y_pre)))) (PreH19 : (0 <= (Znth 0 digits_2 0))) (PreH20 : ((Znth 0 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 1 digits_2 0))) (PreH22 : ((Znth 1 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 2 digits_2 0))) (PreH24 : ((Znth 2 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 3 digits_2 0))) (PreH26 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9)
.

Definition next_year_entail_wit_3_6_split_goal_4 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < prev_pre)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH4 : (v <= 9)) (PreH5 : (1000 <= y_pre)) (PreH6 : (y_pre <= 9999)) (PreH7 : (1000 <= prev_pre)) (PreH8 : (prev_pre <= 2011)) (PreH9 : (0 <= pos)) (PreH10 : (pos < 4)) (PreH11 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH12 : ((DigitLower (pos)) <= v)) (PreH13 : (v <= 10)) (PreH14 : ((-1) <= best)) (PreH15 : (best <= 2011)) (PreH16 : (BestScanned y_pre prev_pre pos v best )) (PreH17 : (v = (DigitLower (pos)))) (PreH18 : (digits_2 = (YearDigits (y_pre)))) (PreH19 : (0 <= (Znth 0 digits_2 0))) (PreH20 : ((Znth 0 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 1 digits_2 0))) (PreH22 : ((Znth 1 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 2 digits_2 0))) (PreH24 : ((Znth 2 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 3 digits_2 0))) (PreH26 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0))
.

Definition next_year_entail_wit_3_6_split_goal_5 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < prev_pre)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH4 : (v <= 9)) (PreH5 : (1000 <= y_pre)) (PreH6 : (y_pre <= 9999)) (PreH7 : (1000 <= prev_pre)) (PreH8 : (prev_pre <= 2011)) (PreH9 : (0 <= pos)) (PreH10 : (pos < 4)) (PreH11 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH12 : ((DigitLower (pos)) <= v)) (PreH13 : (v <= 10)) (PreH14 : ((-1) <= best)) (PreH15 : (best <= 2011)) (PreH16 : (BestScanned y_pre prev_pre pos v best )) (PreH17 : (v = (DigitLower (pos)))) (PreH18 : (digits_2 = (YearDigits (y_pre)))) (PreH19 : (0 <= (Znth 0 digits_2 0))) (PreH20 : ((Znth 0 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 1 digits_2 0))) (PreH22 : ((Znth 1 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 2 digits_2 0))) (PreH24 : ((Znth 2 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 3 digits_2 0))) (PreH26 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9)
.

Definition next_year_entail_wit_3_6_split_goal_6 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < prev_pre)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH4 : (v <= 9)) (PreH5 : (1000 <= y_pre)) (PreH6 : (y_pre <= 9999)) (PreH7 : (1000 <= prev_pre)) (PreH8 : (prev_pre <= 2011)) (PreH9 : (0 <= pos)) (PreH10 : (pos < 4)) (PreH11 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH12 : ((DigitLower (pos)) <= v)) (PreH13 : (v <= 10)) (PreH14 : ((-1) <= best)) (PreH15 : (best <= 2011)) (PreH16 : (BestScanned y_pre prev_pre pos v best )) (PreH17 : (v = (DigitLower (pos)))) (PreH18 : (digits_2 = (YearDigits (y_pre)))) (PreH19 : (0 <= (Znth 0 digits_2 0))) (PreH20 : ((Znth 0 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 1 digits_2 0))) (PreH22 : ((Znth 1 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 2 digits_2 0))) (PreH24 : ((Znth 2 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 3 digits_2 0))) (PreH26 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0))
.

Definition next_year_entail_wit_3_6_split_goal_7 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < prev_pre)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH4 : (v <= 9)) (PreH5 : (1000 <= y_pre)) (PreH6 : (y_pre <= 9999)) (PreH7 : (1000 <= prev_pre)) (PreH8 : (prev_pre <= 2011)) (PreH9 : (0 <= pos)) (PreH10 : (pos < 4)) (PreH11 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH12 : ((DigitLower (pos)) <= v)) (PreH13 : (v <= 10)) (PreH14 : ((-1) <= best)) (PreH15 : (best <= 2011)) (PreH16 : (BestScanned y_pre prev_pre pos v best )) (PreH17 : (v = (DigitLower (pos)))) (PreH18 : (digits_2 = (YearDigits (y_pre)))) (PreH19 : (0 <= (Znth 0 digits_2 0))) (PreH20 : ((Znth 0 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 1 digits_2 0))) (PreH22 : ((Znth 1 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 2 digits_2 0))) (PreH24 : ((Znth 2 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 3 digits_2 0))) (PreH26 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9)
.

Definition next_year_entail_wit_3_6_split_goal_8 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < prev_pre)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH4 : (v <= 9)) (PreH5 : (1000 <= y_pre)) (PreH6 : (y_pre <= 9999)) (PreH7 : (1000 <= prev_pre)) (PreH8 : (prev_pre <= 2011)) (PreH9 : (0 <= pos)) (PreH10 : (pos < 4)) (PreH11 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH12 : ((DigitLower (pos)) <= v)) (PreH13 : (v <= 10)) (PreH14 : ((-1) <= best)) (PreH15 : (best <= 2011)) (PreH16 : (BestScanned y_pre prev_pre pos v best )) (PreH17 : (v = (DigitLower (pos)))) (PreH18 : (digits_2 = (YearDigits (y_pre)))) (PreH19 : (0 <= (Znth 0 digits_2 0))) (PreH20 : ((Znth 0 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 1 digits_2 0))) (PreH22 : ((Znth 1 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 2 digits_2 0))) (PreH24 : ((Znth 2 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 3 digits_2 0))) (PreH26 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0))
.

Definition next_year_entail_wit_3_6_split_goal_9 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < prev_pre)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH4 : (v <= 9)) (PreH5 : (1000 <= y_pre)) (PreH6 : (y_pre <= 9999)) (PreH7 : (1000 <= prev_pre)) (PreH8 : (prev_pre <= 2011)) (PreH9 : (0 <= pos)) (PreH10 : (pos < 4)) (PreH11 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH12 : ((DigitLower (pos)) <= v)) (PreH13 : (v <= 10)) (PreH14 : ((-1) <= best)) (PreH15 : (best <= 2011)) (PreH16 : (BestScanned y_pre prev_pre pos v best )) (PreH17 : (v = (DigitLower (pos)))) (PreH18 : (digits_2 = (YearDigits (y_pre)))) (PreH19 : (0 <= (Znth 0 digits_2 0))) (PreH20 : ((Znth 0 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 1 digits_2 0))) (PreH22 : ((Znth 1 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 2 digits_2 0))) (PreH24 : ((Znth 2 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 3 digits_2 0))) (PreH26 : ((Znth 3 digits_2 0) <= 9)) ,
  (BestScanned y_pre prev_pre pos (v + 1 ) best )
.

Definition next_year_entail_wit_3_6_split_goal_10 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < prev_pre)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH4 : (v <= 9)) (PreH5 : (1000 <= y_pre)) (PreH6 : (y_pre <= 9999)) (PreH7 : (1000 <= prev_pre)) (PreH8 : (prev_pre <= 2011)) (PreH9 : (0 <= pos)) (PreH10 : (pos < 4)) (PreH11 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH12 : ((DigitLower (pos)) <= v)) (PreH13 : (v <= 10)) (PreH14 : ((-1) <= best)) (PreH15 : (best <= 2011)) (PreH16 : (BestScanned y_pre prev_pre pos v best )) (PreH17 : (v = (DigitLower (pos)))) (PreH18 : (digits_2 = (YearDigits (y_pre)))) (PreH19 : (0 <= (Znth 0 digits_2 0))) (PreH20 : ((Znth 0 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 1 digits_2 0))) (PreH22 : ((Znth 1 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 2 digits_2 0))) (PreH24 : ((Znth 2 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 3 digits_2 0))) (PreH26 : ((Znth 3 digits_2 0) <= 9)) ,
  ((replace_Znth (pos) (v) (digits_2)) = (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)))
.

Definition next_year_entail_wit_3_7 := 
(
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < 1000)) (PreH2 : (v <= 9)) (PreH3 : (1000 <= y_pre)) (PreH4 : (y_pre <= 9999)) (PreH5 : (1000 <= prev_pre)) (PreH6 : (prev_pre <= 2011)) (PreH7 : (0 <= pos)) (PreH8 : (pos < 4)) (PreH9 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH10 : ((DigitLower (pos)) <= v)) (PreH11 : (v <= 10)) (PreH12 : ((-1) <= best)) (PreH13 : (best <= 2011)) (PreH14 : (BestScanned y_pre prev_pre pos v best )) (PreH15 : ((DigitLower (pos)) < v)) (PreH16 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH17 : (0 <= (Znth 0 digits_2 0))) (PreH18 : ((Znth 0 digits_2 0) <= 9)) (PreH19 : (0 <= (Znth 1 digits_2 0))) (PreH20 : ((Znth 1 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 2 digits_2 0))) (PreH22 : ((Znth 2 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 3 digits_2 0))) (PreH24 : ((Znth 3 digits_2 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits_2)) )
|--
  EX (digits: (@list Z)) ,
  “ (1000 <= y_pre) ” 
  &&  “ (y_pre <= 9999) ” 
  &&  “ (1000 <= prev_pre) ” 
  &&  “ (prev_pre <= 2011) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < 4) ” 
  &&  “ (old = (Znth pos (YearDigits (y_pre)) 0)) ” 
  &&  “ ((DigitLower (pos)) <= (v + 1 )) ” 
  &&  “ ((v + 1 ) <= 10) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 2011) ” 
  &&  “ (BestScanned y_pre prev_pre pos (v + 1 ) best ) ” 
  &&  “ ((DigitLower (pos)) < (v + 1 )) ” 
  &&  “ (digits = (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre))))) ” 
  &&  “ (0 <= (Znth 0 digits 0)) ” 
  &&  “ ((Znth 0 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 digits 0)) ” 
  &&  “ ((Znth 1 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 digits 0)) ” 
  &&  “ ((Znth 2 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 digits 0)) ” 
  &&  “ ((Znth 3 digits 0) <= 9) ”
  &&  (IntArray.full ( &( "d" ) ) 4 digits )
) \/
(
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < 1000)) (PreH2 : (v <= 9)) (PreH3 : (1000 <= y_pre)) (PreH4 : (y_pre <= 9999)) (PreH5 : (1000 <= prev_pre)) (PreH6 : (prev_pre <= 2011)) (PreH7 : (0 <= pos)) (PreH8 : (pos < 4)) (PreH9 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH10 : ((DigitLower (pos)) <= v)) (PreH11 : (v <= 10)) (PreH12 : ((-1) <= best)) (PreH13 : (best <= 2011)) (PreH14 : (BestScanned y_pre prev_pre pos v best )) (PreH15 : ((DigitLower (pos)) < v)) (PreH16 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH17 : (0 <= (Znth 0 digits_2 0))) (PreH18 : ((Znth 0 digits_2 0) <= 9)) (PreH19 : (0 <= (Znth 1 digits_2 0))) (PreH20 : ((Znth 1 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 2 digits_2 0))) (PreH22 : ((Znth 2 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 3 digits_2 0))) (PreH24 : ((Znth 3 digits_2 0) <= 9)) ,
  TT && emp 
|--
  “ ((Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0)) ” 
  &&  “ ((Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0)) ” 
  &&  “ ((Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0)) ” 
  &&  “ ((Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9) ” 
  &&  “ (0 <= (Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0)) ” 
  &&  “ (BestScanned y_pre prev_pre pos (v + 1 ) best ) ” 
  &&  “ ((replace_Znth (pos) (v) (digits_2)) = (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre))))) ”
  &&  emp
).

Definition next_year_entail_wit_3_7_split_goal_1 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < 1000)) (PreH2 : (v <= 9)) (PreH3 : (1000 <= y_pre)) (PreH4 : (y_pre <= 9999)) (PreH5 : (1000 <= prev_pre)) (PreH6 : (prev_pre <= 2011)) (PreH7 : (0 <= pos)) (PreH8 : (pos < 4)) (PreH9 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH10 : ((DigitLower (pos)) <= v)) (PreH11 : (v <= 10)) (PreH12 : ((-1) <= best)) (PreH13 : (best <= 2011)) (PreH14 : (BestScanned y_pre prev_pre pos v best )) (PreH15 : ((DigitLower (pos)) < v)) (PreH16 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH17 : (0 <= (Znth 0 digits_2 0))) (PreH18 : ((Znth 0 digits_2 0) <= 9)) (PreH19 : (0 <= (Znth 1 digits_2 0))) (PreH20 : ((Znth 1 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 2 digits_2 0))) (PreH22 : ((Znth 2 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 3 digits_2 0))) (PreH24 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9)
.

Definition next_year_entail_wit_3_7_split_goal_2 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < 1000)) (PreH2 : (v <= 9)) (PreH3 : (1000 <= y_pre)) (PreH4 : (y_pre <= 9999)) (PreH5 : (1000 <= prev_pre)) (PreH6 : (prev_pre <= 2011)) (PreH7 : (0 <= pos)) (PreH8 : (pos < 4)) (PreH9 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH10 : ((DigitLower (pos)) <= v)) (PreH11 : (v <= 10)) (PreH12 : ((-1) <= best)) (PreH13 : (best <= 2011)) (PreH14 : (BestScanned y_pre prev_pre pos v best )) (PreH15 : ((DigitLower (pos)) < v)) (PreH16 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH17 : (0 <= (Znth 0 digits_2 0))) (PreH18 : ((Znth 0 digits_2 0) <= 9)) (PreH19 : (0 <= (Znth 1 digits_2 0))) (PreH20 : ((Znth 1 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 2 digits_2 0))) (PreH22 : ((Znth 2 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 3 digits_2 0))) (PreH24 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0))
.

Definition next_year_entail_wit_3_7_split_goal_3 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < 1000)) (PreH2 : (v <= 9)) (PreH3 : (1000 <= y_pre)) (PreH4 : (y_pre <= 9999)) (PreH5 : (1000 <= prev_pre)) (PreH6 : (prev_pre <= 2011)) (PreH7 : (0 <= pos)) (PreH8 : (pos < 4)) (PreH9 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH10 : ((DigitLower (pos)) <= v)) (PreH11 : (v <= 10)) (PreH12 : ((-1) <= best)) (PreH13 : (best <= 2011)) (PreH14 : (BestScanned y_pre prev_pre pos v best )) (PreH15 : ((DigitLower (pos)) < v)) (PreH16 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH17 : (0 <= (Znth 0 digits_2 0))) (PreH18 : ((Znth 0 digits_2 0) <= 9)) (PreH19 : (0 <= (Znth 1 digits_2 0))) (PreH20 : ((Znth 1 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 2 digits_2 0))) (PreH22 : ((Znth 2 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 3 digits_2 0))) (PreH24 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9)
.

Definition next_year_entail_wit_3_7_split_goal_4 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < 1000)) (PreH2 : (v <= 9)) (PreH3 : (1000 <= y_pre)) (PreH4 : (y_pre <= 9999)) (PreH5 : (1000 <= prev_pre)) (PreH6 : (prev_pre <= 2011)) (PreH7 : (0 <= pos)) (PreH8 : (pos < 4)) (PreH9 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH10 : ((DigitLower (pos)) <= v)) (PreH11 : (v <= 10)) (PreH12 : ((-1) <= best)) (PreH13 : (best <= 2011)) (PreH14 : (BestScanned y_pre prev_pre pos v best )) (PreH15 : ((DigitLower (pos)) < v)) (PreH16 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH17 : (0 <= (Znth 0 digits_2 0))) (PreH18 : ((Znth 0 digits_2 0) <= 9)) (PreH19 : (0 <= (Znth 1 digits_2 0))) (PreH20 : ((Znth 1 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 2 digits_2 0))) (PreH22 : ((Znth 2 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 3 digits_2 0))) (PreH24 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0))
.

Definition next_year_entail_wit_3_7_split_goal_5 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < 1000)) (PreH2 : (v <= 9)) (PreH3 : (1000 <= y_pre)) (PreH4 : (y_pre <= 9999)) (PreH5 : (1000 <= prev_pre)) (PreH6 : (prev_pre <= 2011)) (PreH7 : (0 <= pos)) (PreH8 : (pos < 4)) (PreH9 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH10 : ((DigitLower (pos)) <= v)) (PreH11 : (v <= 10)) (PreH12 : ((-1) <= best)) (PreH13 : (best <= 2011)) (PreH14 : (BestScanned y_pre prev_pre pos v best )) (PreH15 : ((DigitLower (pos)) < v)) (PreH16 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH17 : (0 <= (Znth 0 digits_2 0))) (PreH18 : ((Znth 0 digits_2 0) <= 9)) (PreH19 : (0 <= (Znth 1 digits_2 0))) (PreH20 : ((Znth 1 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 2 digits_2 0))) (PreH22 : ((Znth 2 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 3 digits_2 0))) (PreH24 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9)
.

Definition next_year_entail_wit_3_7_split_goal_6 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < 1000)) (PreH2 : (v <= 9)) (PreH3 : (1000 <= y_pre)) (PreH4 : (y_pre <= 9999)) (PreH5 : (1000 <= prev_pre)) (PreH6 : (prev_pre <= 2011)) (PreH7 : (0 <= pos)) (PreH8 : (pos < 4)) (PreH9 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH10 : ((DigitLower (pos)) <= v)) (PreH11 : (v <= 10)) (PreH12 : ((-1) <= best)) (PreH13 : (best <= 2011)) (PreH14 : (BestScanned y_pre prev_pre pos v best )) (PreH15 : ((DigitLower (pos)) < v)) (PreH16 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH17 : (0 <= (Znth 0 digits_2 0))) (PreH18 : ((Znth 0 digits_2 0) <= 9)) (PreH19 : (0 <= (Znth 1 digits_2 0))) (PreH20 : ((Znth 1 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 2 digits_2 0))) (PreH22 : ((Znth 2 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 3 digits_2 0))) (PreH24 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0))
.

Definition next_year_entail_wit_3_7_split_goal_7 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < 1000)) (PreH2 : (v <= 9)) (PreH3 : (1000 <= y_pre)) (PreH4 : (y_pre <= 9999)) (PreH5 : (1000 <= prev_pre)) (PreH6 : (prev_pre <= 2011)) (PreH7 : (0 <= pos)) (PreH8 : (pos < 4)) (PreH9 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH10 : ((DigitLower (pos)) <= v)) (PreH11 : (v <= 10)) (PreH12 : ((-1) <= best)) (PreH13 : (best <= 2011)) (PreH14 : (BestScanned y_pre prev_pre pos v best )) (PreH15 : ((DigitLower (pos)) < v)) (PreH16 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH17 : (0 <= (Znth 0 digits_2 0))) (PreH18 : ((Znth 0 digits_2 0) <= 9)) (PreH19 : (0 <= (Znth 1 digits_2 0))) (PreH20 : ((Znth 1 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 2 digits_2 0))) (PreH22 : ((Znth 2 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 3 digits_2 0))) (PreH24 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9)
.

Definition next_year_entail_wit_3_7_split_goal_8 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < 1000)) (PreH2 : (v <= 9)) (PreH3 : (1000 <= y_pre)) (PreH4 : (y_pre <= 9999)) (PreH5 : (1000 <= prev_pre)) (PreH6 : (prev_pre <= 2011)) (PreH7 : (0 <= pos)) (PreH8 : (pos < 4)) (PreH9 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH10 : ((DigitLower (pos)) <= v)) (PreH11 : (v <= 10)) (PreH12 : ((-1) <= best)) (PreH13 : (best <= 2011)) (PreH14 : (BestScanned y_pre prev_pre pos v best )) (PreH15 : ((DigitLower (pos)) < v)) (PreH16 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH17 : (0 <= (Znth 0 digits_2 0))) (PreH18 : ((Znth 0 digits_2 0) <= 9)) (PreH19 : (0 <= (Znth 1 digits_2 0))) (PreH20 : ((Znth 1 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 2 digits_2 0))) (PreH22 : ((Znth 2 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 3 digits_2 0))) (PreH24 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0))
.

Definition next_year_entail_wit_3_7_split_goal_9 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < 1000)) (PreH2 : (v <= 9)) (PreH3 : (1000 <= y_pre)) (PreH4 : (y_pre <= 9999)) (PreH5 : (1000 <= prev_pre)) (PreH6 : (prev_pre <= 2011)) (PreH7 : (0 <= pos)) (PreH8 : (pos < 4)) (PreH9 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH10 : ((DigitLower (pos)) <= v)) (PreH11 : (v <= 10)) (PreH12 : ((-1) <= best)) (PreH13 : (best <= 2011)) (PreH14 : (BestScanned y_pre prev_pre pos v best )) (PreH15 : ((DigitLower (pos)) < v)) (PreH16 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH17 : (0 <= (Znth 0 digits_2 0))) (PreH18 : ((Znth 0 digits_2 0) <= 9)) (PreH19 : (0 <= (Znth 1 digits_2 0))) (PreH20 : ((Znth 1 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 2 digits_2 0))) (PreH22 : ((Znth 2 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 3 digits_2 0))) (PreH24 : ((Znth 3 digits_2 0) <= 9)) ,
  (BestScanned y_pre prev_pre pos (v + 1 ) best )
.

Definition next_year_entail_wit_3_7_split_goal_10 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < 1000)) (PreH2 : (v <= 9)) (PreH3 : (1000 <= y_pre)) (PreH4 : (y_pre <= 9999)) (PreH5 : (1000 <= prev_pre)) (PreH6 : (prev_pre <= 2011)) (PreH7 : (0 <= pos)) (PreH8 : (pos < 4)) (PreH9 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH10 : ((DigitLower (pos)) <= v)) (PreH11 : (v <= 10)) (PreH12 : ((-1) <= best)) (PreH13 : (best <= 2011)) (PreH14 : (BestScanned y_pre prev_pre pos v best )) (PreH15 : ((DigitLower (pos)) < v)) (PreH16 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH17 : (0 <= (Znth 0 digits_2 0))) (PreH18 : ((Znth 0 digits_2 0) <= 9)) (PreH19 : (0 <= (Znth 1 digits_2 0))) (PreH20 : ((Znth 1 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 2 digits_2 0))) (PreH22 : ((Znth 2 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 3 digits_2 0))) (PreH24 : ((Znth 3 digits_2 0) <= 9)) ,
  ((replace_Znth (pos) (v) (digits_2)) = (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))))
.

Definition next_year_entail_wit_3_8 := 
(
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < 1000)) (PreH2 : (v <= 9)) (PreH3 : (1000 <= y_pre)) (PreH4 : (y_pre <= 9999)) (PreH5 : (1000 <= prev_pre)) (PreH6 : (prev_pre <= 2011)) (PreH7 : (0 <= pos)) (PreH8 : (pos < 4)) (PreH9 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH10 : ((DigitLower (pos)) <= v)) (PreH11 : (v <= 10)) (PreH12 : ((-1) <= best)) (PreH13 : (best <= 2011)) (PreH14 : (BestScanned y_pre prev_pre pos v best )) (PreH15 : (v = (DigitLower (pos)))) (PreH16 : (digits_2 = (YearDigits (y_pre)))) (PreH17 : (0 <= (Znth 0 digits_2 0))) (PreH18 : ((Znth 0 digits_2 0) <= 9)) (PreH19 : (0 <= (Znth 1 digits_2 0))) (PreH20 : ((Znth 1 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 2 digits_2 0))) (PreH22 : ((Znth 2 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 3 digits_2 0))) (PreH24 : ((Znth 3 digits_2 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits_2)) )
|--
  EX (digits: (@list Z)) ,
  “ (1000 <= y_pre) ” 
  &&  “ (y_pre <= 9999) ” 
  &&  “ (1000 <= prev_pre) ” 
  &&  “ (prev_pre <= 2011) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < 4) ” 
  &&  “ (old = (Znth pos (YearDigits (y_pre)) 0)) ” 
  &&  “ ((DigitLower (pos)) <= (v + 1 )) ” 
  &&  “ ((v + 1 ) <= 10) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 2011) ” 
  &&  “ (BestScanned y_pre prev_pre pos (v + 1 ) best ) ” 
  &&  “ ((DigitLower (pos)) < (v + 1 )) ” 
  &&  “ (digits = (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre))))) ” 
  &&  “ (0 <= (Znth 0 digits 0)) ” 
  &&  “ ((Znth 0 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 digits 0)) ” 
  &&  “ ((Znth 1 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 digits 0)) ” 
  &&  “ ((Znth 2 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 digits 0)) ” 
  &&  “ ((Znth 3 digits 0) <= 9) ”
  &&  (IntArray.full ( &( "d" ) ) 4 digits )
) \/
(
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < 1000)) (PreH2 : (v <= 9)) (PreH3 : (1000 <= y_pre)) (PreH4 : (y_pre <= 9999)) (PreH5 : (1000 <= prev_pre)) (PreH6 : (prev_pre <= 2011)) (PreH7 : (0 <= pos)) (PreH8 : (pos < 4)) (PreH9 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH10 : ((DigitLower (pos)) <= v)) (PreH11 : (v <= 10)) (PreH12 : ((-1) <= best)) (PreH13 : (best <= 2011)) (PreH14 : (BestScanned y_pre prev_pre pos v best )) (PreH15 : (v = (DigitLower (pos)))) (PreH16 : (digits_2 = (YearDigits (y_pre)))) (PreH17 : (0 <= (Znth 0 digits_2 0))) (PreH18 : ((Znth 0 digits_2 0) <= 9)) (PreH19 : (0 <= (Znth 1 digits_2 0))) (PreH20 : ((Znth 1 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 2 digits_2 0))) (PreH22 : ((Znth 2 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 3 digits_2 0))) (PreH24 : ((Znth 3 digits_2 0) <= 9)) ,
  TT && emp 
|--
  “ ((Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0)) ” 
  &&  “ ((Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0)) ” 
  &&  “ ((Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0)) ” 
  &&  “ ((Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0)) ” 
  &&  “ (BestScanned y_pre prev_pre pos (v + 1 ) best ) ” 
  &&  “ ((replace_Znth (pos) (v) (digits_2)) = (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2))) ”
  &&  emp
).

Definition next_year_entail_wit_3_8_split_goal_1 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < 1000)) (PreH2 : (v <= 9)) (PreH3 : (1000 <= y_pre)) (PreH4 : (y_pre <= 9999)) (PreH5 : (1000 <= prev_pre)) (PreH6 : (prev_pre <= 2011)) (PreH7 : (0 <= pos)) (PreH8 : (pos < 4)) (PreH9 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH10 : ((DigitLower (pos)) <= v)) (PreH11 : (v <= 10)) (PreH12 : ((-1) <= best)) (PreH13 : (best <= 2011)) (PreH14 : (BestScanned y_pre prev_pre pos v best )) (PreH15 : (v = (DigitLower (pos)))) (PreH16 : (digits_2 = (YearDigits (y_pre)))) (PreH17 : (0 <= (Znth 0 digits_2 0))) (PreH18 : ((Znth 0 digits_2 0) <= 9)) (PreH19 : (0 <= (Znth 1 digits_2 0))) (PreH20 : ((Znth 1 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 2 digits_2 0))) (PreH22 : ((Znth 2 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 3 digits_2 0))) (PreH24 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9)
.

Definition next_year_entail_wit_3_8_split_goal_2 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < 1000)) (PreH2 : (v <= 9)) (PreH3 : (1000 <= y_pre)) (PreH4 : (y_pre <= 9999)) (PreH5 : (1000 <= prev_pre)) (PreH6 : (prev_pre <= 2011)) (PreH7 : (0 <= pos)) (PreH8 : (pos < 4)) (PreH9 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH10 : ((DigitLower (pos)) <= v)) (PreH11 : (v <= 10)) (PreH12 : ((-1) <= best)) (PreH13 : (best <= 2011)) (PreH14 : (BestScanned y_pre prev_pre pos v best )) (PreH15 : (v = (DigitLower (pos)))) (PreH16 : (digits_2 = (YearDigits (y_pre)))) (PreH17 : (0 <= (Znth 0 digits_2 0))) (PreH18 : ((Znth 0 digits_2 0) <= 9)) (PreH19 : (0 <= (Znth 1 digits_2 0))) (PreH20 : ((Znth 1 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 2 digits_2 0))) (PreH22 : ((Znth 2 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 3 digits_2 0))) (PreH24 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0))
.

Definition next_year_entail_wit_3_8_split_goal_3 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < 1000)) (PreH2 : (v <= 9)) (PreH3 : (1000 <= y_pre)) (PreH4 : (y_pre <= 9999)) (PreH5 : (1000 <= prev_pre)) (PreH6 : (prev_pre <= 2011)) (PreH7 : (0 <= pos)) (PreH8 : (pos < 4)) (PreH9 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH10 : ((DigitLower (pos)) <= v)) (PreH11 : (v <= 10)) (PreH12 : ((-1) <= best)) (PreH13 : (best <= 2011)) (PreH14 : (BestScanned y_pre prev_pre pos v best )) (PreH15 : (v = (DigitLower (pos)))) (PreH16 : (digits_2 = (YearDigits (y_pre)))) (PreH17 : (0 <= (Znth 0 digits_2 0))) (PreH18 : ((Znth 0 digits_2 0) <= 9)) (PreH19 : (0 <= (Znth 1 digits_2 0))) (PreH20 : ((Znth 1 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 2 digits_2 0))) (PreH22 : ((Znth 2 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 3 digits_2 0))) (PreH24 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9)
.

Definition next_year_entail_wit_3_8_split_goal_4 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < 1000)) (PreH2 : (v <= 9)) (PreH3 : (1000 <= y_pre)) (PreH4 : (y_pre <= 9999)) (PreH5 : (1000 <= prev_pre)) (PreH6 : (prev_pre <= 2011)) (PreH7 : (0 <= pos)) (PreH8 : (pos < 4)) (PreH9 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH10 : ((DigitLower (pos)) <= v)) (PreH11 : (v <= 10)) (PreH12 : ((-1) <= best)) (PreH13 : (best <= 2011)) (PreH14 : (BestScanned y_pre prev_pre pos v best )) (PreH15 : (v = (DigitLower (pos)))) (PreH16 : (digits_2 = (YearDigits (y_pre)))) (PreH17 : (0 <= (Znth 0 digits_2 0))) (PreH18 : ((Znth 0 digits_2 0) <= 9)) (PreH19 : (0 <= (Znth 1 digits_2 0))) (PreH20 : ((Znth 1 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 2 digits_2 0))) (PreH22 : ((Znth 2 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 3 digits_2 0))) (PreH24 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0))
.

Definition next_year_entail_wit_3_8_split_goal_5 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < 1000)) (PreH2 : (v <= 9)) (PreH3 : (1000 <= y_pre)) (PreH4 : (y_pre <= 9999)) (PreH5 : (1000 <= prev_pre)) (PreH6 : (prev_pre <= 2011)) (PreH7 : (0 <= pos)) (PreH8 : (pos < 4)) (PreH9 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH10 : ((DigitLower (pos)) <= v)) (PreH11 : (v <= 10)) (PreH12 : ((-1) <= best)) (PreH13 : (best <= 2011)) (PreH14 : (BestScanned y_pre prev_pre pos v best )) (PreH15 : (v = (DigitLower (pos)))) (PreH16 : (digits_2 = (YearDigits (y_pre)))) (PreH17 : (0 <= (Znth 0 digits_2 0))) (PreH18 : ((Znth 0 digits_2 0) <= 9)) (PreH19 : (0 <= (Znth 1 digits_2 0))) (PreH20 : ((Znth 1 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 2 digits_2 0))) (PreH22 : ((Znth 2 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 3 digits_2 0))) (PreH24 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9)
.

Definition next_year_entail_wit_3_8_split_goal_6 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < 1000)) (PreH2 : (v <= 9)) (PreH3 : (1000 <= y_pre)) (PreH4 : (y_pre <= 9999)) (PreH5 : (1000 <= prev_pre)) (PreH6 : (prev_pre <= 2011)) (PreH7 : (0 <= pos)) (PreH8 : (pos < 4)) (PreH9 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH10 : ((DigitLower (pos)) <= v)) (PreH11 : (v <= 10)) (PreH12 : ((-1) <= best)) (PreH13 : (best <= 2011)) (PreH14 : (BestScanned y_pre prev_pre pos v best )) (PreH15 : (v = (DigitLower (pos)))) (PreH16 : (digits_2 = (YearDigits (y_pre)))) (PreH17 : (0 <= (Znth 0 digits_2 0))) (PreH18 : ((Znth 0 digits_2 0) <= 9)) (PreH19 : (0 <= (Znth 1 digits_2 0))) (PreH20 : ((Znth 1 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 2 digits_2 0))) (PreH22 : ((Znth 2 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 3 digits_2 0))) (PreH24 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0))
.

Definition next_year_entail_wit_3_8_split_goal_7 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < 1000)) (PreH2 : (v <= 9)) (PreH3 : (1000 <= y_pre)) (PreH4 : (y_pre <= 9999)) (PreH5 : (1000 <= prev_pre)) (PreH6 : (prev_pre <= 2011)) (PreH7 : (0 <= pos)) (PreH8 : (pos < 4)) (PreH9 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH10 : ((DigitLower (pos)) <= v)) (PreH11 : (v <= 10)) (PreH12 : ((-1) <= best)) (PreH13 : (best <= 2011)) (PreH14 : (BestScanned y_pre prev_pre pos v best )) (PreH15 : (v = (DigitLower (pos)))) (PreH16 : (digits_2 = (YearDigits (y_pre)))) (PreH17 : (0 <= (Znth 0 digits_2 0))) (PreH18 : ((Znth 0 digits_2 0) <= 9)) (PreH19 : (0 <= (Znth 1 digits_2 0))) (PreH20 : ((Znth 1 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 2 digits_2 0))) (PreH22 : ((Znth 2 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 3 digits_2 0))) (PreH24 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9)
.

Definition next_year_entail_wit_3_8_split_goal_8 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < 1000)) (PreH2 : (v <= 9)) (PreH3 : (1000 <= y_pre)) (PreH4 : (y_pre <= 9999)) (PreH5 : (1000 <= prev_pre)) (PreH6 : (prev_pre <= 2011)) (PreH7 : (0 <= pos)) (PreH8 : (pos < 4)) (PreH9 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH10 : ((DigitLower (pos)) <= v)) (PreH11 : (v <= 10)) (PreH12 : ((-1) <= best)) (PreH13 : (best <= 2011)) (PreH14 : (BestScanned y_pre prev_pre pos v best )) (PreH15 : (v = (DigitLower (pos)))) (PreH16 : (digits_2 = (YearDigits (y_pre)))) (PreH17 : (0 <= (Znth 0 digits_2 0))) (PreH18 : ((Znth 0 digits_2 0) <= 9)) (PreH19 : (0 <= (Znth 1 digits_2 0))) (PreH20 : ((Znth 1 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 2 digits_2 0))) (PreH22 : ((Znth 2 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 3 digits_2 0))) (PreH24 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0))
.

Definition next_year_entail_wit_3_8_split_goal_9 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < 1000)) (PreH2 : (v <= 9)) (PreH3 : (1000 <= y_pre)) (PreH4 : (y_pre <= 9999)) (PreH5 : (1000 <= prev_pre)) (PreH6 : (prev_pre <= 2011)) (PreH7 : (0 <= pos)) (PreH8 : (pos < 4)) (PreH9 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH10 : ((DigitLower (pos)) <= v)) (PreH11 : (v <= 10)) (PreH12 : ((-1) <= best)) (PreH13 : (best <= 2011)) (PreH14 : (BestScanned y_pre prev_pre pos v best )) (PreH15 : (v = (DigitLower (pos)))) (PreH16 : (digits_2 = (YearDigits (y_pre)))) (PreH17 : (0 <= (Znth 0 digits_2 0))) (PreH18 : ((Znth 0 digits_2 0) <= 9)) (PreH19 : (0 <= (Znth 1 digits_2 0))) (PreH20 : ((Znth 1 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 2 digits_2 0))) (PreH22 : ((Znth 2 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 3 digits_2 0))) (PreH24 : ((Znth 3 digits_2 0) <= 9)) ,
  (BestScanned y_pre prev_pre pos (v + 1 ) best )
.

Definition next_year_entail_wit_3_8_split_goal_10 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) < 1000)) (PreH2 : (v <= 9)) (PreH3 : (1000 <= y_pre)) (PreH4 : (y_pre <= 9999)) (PreH5 : (1000 <= prev_pre)) (PreH6 : (prev_pre <= 2011)) (PreH7 : (0 <= pos)) (PreH8 : (pos < 4)) (PreH9 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH10 : ((DigitLower (pos)) <= v)) (PreH11 : (v <= 10)) (PreH12 : ((-1) <= best)) (PreH13 : (best <= 2011)) (PreH14 : (BestScanned y_pre prev_pre pos v best )) (PreH15 : (v = (DigitLower (pos)))) (PreH16 : (digits_2 = (YearDigits (y_pre)))) (PreH17 : (0 <= (Znth 0 digits_2 0))) (PreH18 : ((Znth 0 digits_2 0) <= 9)) (PreH19 : (0 <= (Znth 1 digits_2 0))) (PreH20 : ((Znth 1 digits_2 0) <= 9)) (PreH21 : (0 <= (Znth 2 digits_2 0))) (PreH22 : ((Znth 2 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 3 digits_2 0))) (PreH24 : ((Znth 3 digits_2 0) <= 9)) ,
  ((replace_Znth (pos) (v) (digits_2)) = (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)))
.

Definition next_year_entail_wit_3_9 := 
(
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) > 2011)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH3 : (v <= 9)) (PreH4 : (1000 <= y_pre)) (PreH5 : (y_pre <= 9999)) (PreH6 : (1000 <= prev_pre)) (PreH7 : (prev_pre <= 2011)) (PreH8 : (0 <= pos)) (PreH9 : (pos < 4)) (PreH10 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH11 : ((DigitLower (pos)) <= v)) (PreH12 : (v <= 10)) (PreH13 : ((-1) <= best)) (PreH14 : (best <= 2011)) (PreH15 : (BestScanned y_pre prev_pre pos v best )) (PreH16 : (v = (DigitLower (pos)))) (PreH17 : (digits_2 = (YearDigits (y_pre)))) (PreH18 : (0 <= (Znth 0 digits_2 0))) (PreH19 : ((Znth 0 digits_2 0) <= 9)) (PreH20 : (0 <= (Znth 1 digits_2 0))) (PreH21 : ((Znth 1 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 2 digits_2 0))) (PreH23 : ((Znth 2 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 3 digits_2 0))) (PreH25 : ((Znth 3 digits_2 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits_2)) )
|--
  EX (digits: (@list Z)) ,
  “ (1000 <= y_pre) ” 
  &&  “ (y_pre <= 9999) ” 
  &&  “ (1000 <= prev_pre) ” 
  &&  “ (prev_pre <= 2011) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < 4) ” 
  &&  “ (old = (Znth pos (YearDigits (y_pre)) 0)) ” 
  &&  “ ((DigitLower (pos)) <= (v + 1 )) ” 
  &&  “ ((v + 1 ) <= 10) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 2011) ” 
  &&  “ (BestScanned y_pre prev_pre pos (v + 1 ) best ) ” 
  &&  “ ((DigitLower (pos)) < (v + 1 )) ” 
  &&  “ (digits = (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre))))) ” 
  &&  “ (0 <= (Znth 0 digits 0)) ” 
  &&  “ ((Znth 0 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 digits 0)) ” 
  &&  “ ((Znth 1 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 digits 0)) ” 
  &&  “ ((Znth 2 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 digits 0)) ” 
  &&  “ ((Znth 3 digits 0) <= 9) ”
  &&  (IntArray.full ( &( "d" ) ) 4 digits )
) \/
(
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) > 2011)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH3 : (v <= 9)) (PreH4 : (1000 <= y_pre)) (PreH5 : (y_pre <= 9999)) (PreH6 : (1000 <= prev_pre)) (PreH7 : (prev_pre <= 2011)) (PreH8 : (0 <= pos)) (PreH9 : (pos < 4)) (PreH10 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH11 : ((DigitLower (pos)) <= v)) (PreH12 : (v <= 10)) (PreH13 : ((-1) <= best)) (PreH14 : (best <= 2011)) (PreH15 : (BestScanned y_pre prev_pre pos v best )) (PreH16 : (v = (DigitLower (pos)))) (PreH17 : (digits_2 = (YearDigits (y_pre)))) (PreH18 : (0 <= (Znth 0 digits_2 0))) (PreH19 : ((Znth 0 digits_2 0) <= 9)) (PreH20 : (0 <= (Znth 1 digits_2 0))) (PreH21 : ((Znth 1 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 2 digits_2 0))) (PreH23 : ((Znth 2 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 3 digits_2 0))) (PreH25 : ((Znth 3 digits_2 0) <= 9)) ,
  TT && emp 
|--
  “ ((Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0)) ” 
  &&  “ ((Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0)) ” 
  &&  “ ((Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0)) ” 
  &&  “ ((Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0)) ” 
  &&  “ (BestScanned y_pre prev_pre pos (v + 1 ) best ) ” 
  &&  “ ((replace_Znth (pos) (v) (digits_2)) = (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2))) ”
  &&  emp
).

Definition next_year_entail_wit_3_9_split_goal_1 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) > 2011)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH3 : (v <= 9)) (PreH4 : (1000 <= y_pre)) (PreH5 : (y_pre <= 9999)) (PreH6 : (1000 <= prev_pre)) (PreH7 : (prev_pre <= 2011)) (PreH8 : (0 <= pos)) (PreH9 : (pos < 4)) (PreH10 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH11 : ((DigitLower (pos)) <= v)) (PreH12 : (v <= 10)) (PreH13 : ((-1) <= best)) (PreH14 : (best <= 2011)) (PreH15 : (BestScanned y_pre prev_pre pos v best )) (PreH16 : (v = (DigitLower (pos)))) (PreH17 : (digits_2 = (YearDigits (y_pre)))) (PreH18 : (0 <= (Znth 0 digits_2 0))) (PreH19 : ((Znth 0 digits_2 0) <= 9)) (PreH20 : (0 <= (Znth 1 digits_2 0))) (PreH21 : ((Znth 1 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 2 digits_2 0))) (PreH23 : ((Znth 2 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 3 digits_2 0))) (PreH25 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9)
.

Definition next_year_entail_wit_3_9_split_goal_2 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) > 2011)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH3 : (v <= 9)) (PreH4 : (1000 <= y_pre)) (PreH5 : (y_pre <= 9999)) (PreH6 : (1000 <= prev_pre)) (PreH7 : (prev_pre <= 2011)) (PreH8 : (0 <= pos)) (PreH9 : (pos < 4)) (PreH10 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH11 : ((DigitLower (pos)) <= v)) (PreH12 : (v <= 10)) (PreH13 : ((-1) <= best)) (PreH14 : (best <= 2011)) (PreH15 : (BestScanned y_pre prev_pre pos v best )) (PreH16 : (v = (DigitLower (pos)))) (PreH17 : (digits_2 = (YearDigits (y_pre)))) (PreH18 : (0 <= (Znth 0 digits_2 0))) (PreH19 : ((Znth 0 digits_2 0) <= 9)) (PreH20 : (0 <= (Znth 1 digits_2 0))) (PreH21 : ((Znth 1 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 2 digits_2 0))) (PreH23 : ((Znth 2 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 3 digits_2 0))) (PreH25 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0))
.

Definition next_year_entail_wit_3_9_split_goal_3 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) > 2011)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH3 : (v <= 9)) (PreH4 : (1000 <= y_pre)) (PreH5 : (y_pre <= 9999)) (PreH6 : (1000 <= prev_pre)) (PreH7 : (prev_pre <= 2011)) (PreH8 : (0 <= pos)) (PreH9 : (pos < 4)) (PreH10 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH11 : ((DigitLower (pos)) <= v)) (PreH12 : (v <= 10)) (PreH13 : ((-1) <= best)) (PreH14 : (best <= 2011)) (PreH15 : (BestScanned y_pre prev_pre pos v best )) (PreH16 : (v = (DigitLower (pos)))) (PreH17 : (digits_2 = (YearDigits (y_pre)))) (PreH18 : (0 <= (Znth 0 digits_2 0))) (PreH19 : ((Znth 0 digits_2 0) <= 9)) (PreH20 : (0 <= (Znth 1 digits_2 0))) (PreH21 : ((Znth 1 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 2 digits_2 0))) (PreH23 : ((Znth 2 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 3 digits_2 0))) (PreH25 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9)
.

Definition next_year_entail_wit_3_9_split_goal_4 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) > 2011)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH3 : (v <= 9)) (PreH4 : (1000 <= y_pre)) (PreH5 : (y_pre <= 9999)) (PreH6 : (1000 <= prev_pre)) (PreH7 : (prev_pre <= 2011)) (PreH8 : (0 <= pos)) (PreH9 : (pos < 4)) (PreH10 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH11 : ((DigitLower (pos)) <= v)) (PreH12 : (v <= 10)) (PreH13 : ((-1) <= best)) (PreH14 : (best <= 2011)) (PreH15 : (BestScanned y_pre prev_pre pos v best )) (PreH16 : (v = (DigitLower (pos)))) (PreH17 : (digits_2 = (YearDigits (y_pre)))) (PreH18 : (0 <= (Znth 0 digits_2 0))) (PreH19 : ((Znth 0 digits_2 0) <= 9)) (PreH20 : (0 <= (Znth 1 digits_2 0))) (PreH21 : ((Znth 1 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 2 digits_2 0))) (PreH23 : ((Znth 2 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 3 digits_2 0))) (PreH25 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0))
.

Definition next_year_entail_wit_3_9_split_goal_5 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) > 2011)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH3 : (v <= 9)) (PreH4 : (1000 <= y_pre)) (PreH5 : (y_pre <= 9999)) (PreH6 : (1000 <= prev_pre)) (PreH7 : (prev_pre <= 2011)) (PreH8 : (0 <= pos)) (PreH9 : (pos < 4)) (PreH10 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH11 : ((DigitLower (pos)) <= v)) (PreH12 : (v <= 10)) (PreH13 : ((-1) <= best)) (PreH14 : (best <= 2011)) (PreH15 : (BestScanned y_pre prev_pre pos v best )) (PreH16 : (v = (DigitLower (pos)))) (PreH17 : (digits_2 = (YearDigits (y_pre)))) (PreH18 : (0 <= (Znth 0 digits_2 0))) (PreH19 : ((Znth 0 digits_2 0) <= 9)) (PreH20 : (0 <= (Znth 1 digits_2 0))) (PreH21 : ((Znth 1 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 2 digits_2 0))) (PreH23 : ((Znth 2 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 3 digits_2 0))) (PreH25 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9)
.

Definition next_year_entail_wit_3_9_split_goal_6 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) > 2011)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH3 : (v <= 9)) (PreH4 : (1000 <= y_pre)) (PreH5 : (y_pre <= 9999)) (PreH6 : (1000 <= prev_pre)) (PreH7 : (prev_pre <= 2011)) (PreH8 : (0 <= pos)) (PreH9 : (pos < 4)) (PreH10 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH11 : ((DigitLower (pos)) <= v)) (PreH12 : (v <= 10)) (PreH13 : ((-1) <= best)) (PreH14 : (best <= 2011)) (PreH15 : (BestScanned y_pre prev_pre pos v best )) (PreH16 : (v = (DigitLower (pos)))) (PreH17 : (digits_2 = (YearDigits (y_pre)))) (PreH18 : (0 <= (Znth 0 digits_2 0))) (PreH19 : ((Znth 0 digits_2 0) <= 9)) (PreH20 : (0 <= (Znth 1 digits_2 0))) (PreH21 : ((Znth 1 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 2 digits_2 0))) (PreH23 : ((Znth 2 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 3 digits_2 0))) (PreH25 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0))
.

Definition next_year_entail_wit_3_9_split_goal_7 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) > 2011)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH3 : (v <= 9)) (PreH4 : (1000 <= y_pre)) (PreH5 : (y_pre <= 9999)) (PreH6 : (1000 <= prev_pre)) (PreH7 : (prev_pre <= 2011)) (PreH8 : (0 <= pos)) (PreH9 : (pos < 4)) (PreH10 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH11 : ((DigitLower (pos)) <= v)) (PreH12 : (v <= 10)) (PreH13 : ((-1) <= best)) (PreH14 : (best <= 2011)) (PreH15 : (BestScanned y_pre prev_pre pos v best )) (PreH16 : (v = (DigitLower (pos)))) (PreH17 : (digits_2 = (YearDigits (y_pre)))) (PreH18 : (0 <= (Znth 0 digits_2 0))) (PreH19 : ((Znth 0 digits_2 0) <= 9)) (PreH20 : (0 <= (Znth 1 digits_2 0))) (PreH21 : ((Znth 1 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 2 digits_2 0))) (PreH23 : ((Znth 2 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 3 digits_2 0))) (PreH25 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9)
.

Definition next_year_entail_wit_3_9_split_goal_8 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) > 2011)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH3 : (v <= 9)) (PreH4 : (1000 <= y_pre)) (PreH5 : (y_pre <= 9999)) (PreH6 : (1000 <= prev_pre)) (PreH7 : (prev_pre <= 2011)) (PreH8 : (0 <= pos)) (PreH9 : (pos < 4)) (PreH10 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH11 : ((DigitLower (pos)) <= v)) (PreH12 : (v <= 10)) (PreH13 : ((-1) <= best)) (PreH14 : (best <= 2011)) (PreH15 : (BestScanned y_pre prev_pre pos v best )) (PreH16 : (v = (DigitLower (pos)))) (PreH17 : (digits_2 = (YearDigits (y_pre)))) (PreH18 : (0 <= (Znth 0 digits_2 0))) (PreH19 : ((Znth 0 digits_2 0) <= 9)) (PreH20 : (0 <= (Znth 1 digits_2 0))) (PreH21 : ((Znth 1 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 2 digits_2 0))) (PreH23 : ((Znth 2 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 3 digits_2 0))) (PreH25 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0))
.

Definition next_year_entail_wit_3_9_split_goal_9 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) > 2011)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH3 : (v <= 9)) (PreH4 : (1000 <= y_pre)) (PreH5 : (y_pre <= 9999)) (PreH6 : (1000 <= prev_pre)) (PreH7 : (prev_pre <= 2011)) (PreH8 : (0 <= pos)) (PreH9 : (pos < 4)) (PreH10 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH11 : ((DigitLower (pos)) <= v)) (PreH12 : (v <= 10)) (PreH13 : ((-1) <= best)) (PreH14 : (best <= 2011)) (PreH15 : (BestScanned y_pre prev_pre pos v best )) (PreH16 : (v = (DigitLower (pos)))) (PreH17 : (digits_2 = (YearDigits (y_pre)))) (PreH18 : (0 <= (Znth 0 digits_2 0))) (PreH19 : ((Znth 0 digits_2 0) <= 9)) (PreH20 : (0 <= (Znth 1 digits_2 0))) (PreH21 : ((Znth 1 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 2 digits_2 0))) (PreH23 : ((Znth 2 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 3 digits_2 0))) (PreH25 : ((Znth 3 digits_2 0) <= 9)) ,
  (BestScanned y_pre prev_pre pos (v + 1 ) best )
.

Definition next_year_entail_wit_3_9_split_goal_10 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) > 2011)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH3 : (v <= 9)) (PreH4 : (1000 <= y_pre)) (PreH5 : (y_pre <= 9999)) (PreH6 : (1000 <= prev_pre)) (PreH7 : (prev_pre <= 2011)) (PreH8 : (0 <= pos)) (PreH9 : (pos < 4)) (PreH10 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH11 : ((DigitLower (pos)) <= v)) (PreH12 : (v <= 10)) (PreH13 : ((-1) <= best)) (PreH14 : (best <= 2011)) (PreH15 : (BestScanned y_pre prev_pre pos v best )) (PreH16 : (v = (DigitLower (pos)))) (PreH17 : (digits_2 = (YearDigits (y_pre)))) (PreH18 : (0 <= (Znth 0 digits_2 0))) (PreH19 : ((Znth 0 digits_2 0) <= 9)) (PreH20 : (0 <= (Znth 1 digits_2 0))) (PreH21 : ((Znth 1 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 2 digits_2 0))) (PreH23 : ((Znth 2 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 3 digits_2 0))) (PreH25 : ((Znth 3 digits_2 0) <= 9)) ,
  ((replace_Znth (pos) (v) (digits_2)) = (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)))
.

Definition next_year_entail_wit_3_10 := 
(
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) > 2011)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH3 : (v <= 9)) (PreH4 : (1000 <= y_pre)) (PreH5 : (y_pre <= 9999)) (PreH6 : (1000 <= prev_pre)) (PreH7 : (prev_pre <= 2011)) (PreH8 : (0 <= pos)) (PreH9 : (pos < 4)) (PreH10 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH11 : ((DigitLower (pos)) <= v)) (PreH12 : (v <= 10)) (PreH13 : ((-1) <= best)) (PreH14 : (best <= 2011)) (PreH15 : (BestScanned y_pre prev_pre pos v best )) (PreH16 : ((DigitLower (pos)) < v)) (PreH17 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH18 : (0 <= (Znth 0 digits_2 0))) (PreH19 : ((Znth 0 digits_2 0) <= 9)) (PreH20 : (0 <= (Znth 1 digits_2 0))) (PreH21 : ((Znth 1 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 2 digits_2 0))) (PreH23 : ((Znth 2 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 3 digits_2 0))) (PreH25 : ((Znth 3 digits_2 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits_2)) )
|--
  EX (digits: (@list Z)) ,
  “ (1000 <= y_pre) ” 
  &&  “ (y_pre <= 9999) ” 
  &&  “ (1000 <= prev_pre) ” 
  &&  “ (prev_pre <= 2011) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < 4) ” 
  &&  “ (old = (Znth pos (YearDigits (y_pre)) 0)) ” 
  &&  “ ((DigitLower (pos)) <= (v + 1 )) ” 
  &&  “ ((v + 1 ) <= 10) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 2011) ” 
  &&  “ (BestScanned y_pre prev_pre pos (v + 1 ) best ) ” 
  &&  “ ((DigitLower (pos)) < (v + 1 )) ” 
  &&  “ (digits = (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre))))) ” 
  &&  “ (0 <= (Znth 0 digits 0)) ” 
  &&  “ ((Znth 0 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 digits 0)) ” 
  &&  “ ((Znth 1 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 digits 0)) ” 
  &&  “ ((Znth 2 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 digits 0)) ” 
  &&  “ ((Znth 3 digits 0) <= 9) ”
  &&  (IntArray.full ( &( "d" ) ) 4 digits )
) \/
(
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) > 2011)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH3 : (v <= 9)) (PreH4 : (1000 <= y_pre)) (PreH5 : (y_pre <= 9999)) (PreH6 : (1000 <= prev_pre)) (PreH7 : (prev_pre <= 2011)) (PreH8 : (0 <= pos)) (PreH9 : (pos < 4)) (PreH10 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH11 : ((DigitLower (pos)) <= v)) (PreH12 : (v <= 10)) (PreH13 : ((-1) <= best)) (PreH14 : (best <= 2011)) (PreH15 : (BestScanned y_pre prev_pre pos v best )) (PreH16 : ((DigitLower (pos)) < v)) (PreH17 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH18 : (0 <= (Znth 0 digits_2 0))) (PreH19 : ((Znth 0 digits_2 0) <= 9)) (PreH20 : (0 <= (Znth 1 digits_2 0))) (PreH21 : ((Znth 1 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 2 digits_2 0))) (PreH23 : ((Znth 2 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 3 digits_2 0))) (PreH25 : ((Znth 3 digits_2 0) <= 9)) ,
  TT && emp 
|--
  “ ((Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0)) ” 
  &&  “ ((Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0)) ” 
  &&  “ ((Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0)) ” 
  &&  “ ((Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9) ” 
  &&  “ (0 <= (Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0)) ” 
  &&  “ (BestScanned y_pre prev_pre pos (v + 1 ) best ) ” 
  &&  “ ((replace_Znth (pos) (v) (digits_2)) = (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre))))) ”
  &&  emp
).

Definition next_year_entail_wit_3_10_split_goal_1 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) > 2011)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH3 : (v <= 9)) (PreH4 : (1000 <= y_pre)) (PreH5 : (y_pre <= 9999)) (PreH6 : (1000 <= prev_pre)) (PreH7 : (prev_pre <= 2011)) (PreH8 : (0 <= pos)) (PreH9 : (pos < 4)) (PreH10 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH11 : ((DigitLower (pos)) <= v)) (PreH12 : (v <= 10)) (PreH13 : ((-1) <= best)) (PreH14 : (best <= 2011)) (PreH15 : (BestScanned y_pre prev_pre pos v best )) (PreH16 : ((DigitLower (pos)) < v)) (PreH17 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH18 : (0 <= (Znth 0 digits_2 0))) (PreH19 : ((Znth 0 digits_2 0) <= 9)) (PreH20 : (0 <= (Znth 1 digits_2 0))) (PreH21 : ((Znth 1 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 2 digits_2 0))) (PreH23 : ((Znth 2 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 3 digits_2 0))) (PreH25 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9)
.

Definition next_year_entail_wit_3_10_split_goal_2 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) > 2011)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH3 : (v <= 9)) (PreH4 : (1000 <= y_pre)) (PreH5 : (y_pre <= 9999)) (PreH6 : (1000 <= prev_pre)) (PreH7 : (prev_pre <= 2011)) (PreH8 : (0 <= pos)) (PreH9 : (pos < 4)) (PreH10 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH11 : ((DigitLower (pos)) <= v)) (PreH12 : (v <= 10)) (PreH13 : ((-1) <= best)) (PreH14 : (best <= 2011)) (PreH15 : (BestScanned y_pre prev_pre pos v best )) (PreH16 : ((DigitLower (pos)) < v)) (PreH17 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH18 : (0 <= (Znth 0 digits_2 0))) (PreH19 : ((Znth 0 digits_2 0) <= 9)) (PreH20 : (0 <= (Znth 1 digits_2 0))) (PreH21 : ((Znth 1 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 2 digits_2 0))) (PreH23 : ((Znth 2 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 3 digits_2 0))) (PreH25 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0))
.

Definition next_year_entail_wit_3_10_split_goal_3 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) > 2011)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH3 : (v <= 9)) (PreH4 : (1000 <= y_pre)) (PreH5 : (y_pre <= 9999)) (PreH6 : (1000 <= prev_pre)) (PreH7 : (prev_pre <= 2011)) (PreH8 : (0 <= pos)) (PreH9 : (pos < 4)) (PreH10 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH11 : ((DigitLower (pos)) <= v)) (PreH12 : (v <= 10)) (PreH13 : ((-1) <= best)) (PreH14 : (best <= 2011)) (PreH15 : (BestScanned y_pre prev_pre pos v best )) (PreH16 : ((DigitLower (pos)) < v)) (PreH17 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH18 : (0 <= (Znth 0 digits_2 0))) (PreH19 : ((Znth 0 digits_2 0) <= 9)) (PreH20 : (0 <= (Znth 1 digits_2 0))) (PreH21 : ((Znth 1 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 2 digits_2 0))) (PreH23 : ((Znth 2 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 3 digits_2 0))) (PreH25 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9)
.

Definition next_year_entail_wit_3_10_split_goal_4 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) > 2011)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH3 : (v <= 9)) (PreH4 : (1000 <= y_pre)) (PreH5 : (y_pre <= 9999)) (PreH6 : (1000 <= prev_pre)) (PreH7 : (prev_pre <= 2011)) (PreH8 : (0 <= pos)) (PreH9 : (pos < 4)) (PreH10 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH11 : ((DigitLower (pos)) <= v)) (PreH12 : (v <= 10)) (PreH13 : ((-1) <= best)) (PreH14 : (best <= 2011)) (PreH15 : (BestScanned y_pre prev_pre pos v best )) (PreH16 : ((DigitLower (pos)) < v)) (PreH17 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH18 : (0 <= (Znth 0 digits_2 0))) (PreH19 : ((Znth 0 digits_2 0) <= 9)) (PreH20 : (0 <= (Znth 1 digits_2 0))) (PreH21 : ((Znth 1 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 2 digits_2 0))) (PreH23 : ((Znth 2 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 3 digits_2 0))) (PreH25 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0))
.

Definition next_year_entail_wit_3_10_split_goal_5 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) > 2011)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH3 : (v <= 9)) (PreH4 : (1000 <= y_pre)) (PreH5 : (y_pre <= 9999)) (PreH6 : (1000 <= prev_pre)) (PreH7 : (prev_pre <= 2011)) (PreH8 : (0 <= pos)) (PreH9 : (pos < 4)) (PreH10 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH11 : ((DigitLower (pos)) <= v)) (PreH12 : (v <= 10)) (PreH13 : ((-1) <= best)) (PreH14 : (best <= 2011)) (PreH15 : (BestScanned y_pre prev_pre pos v best )) (PreH16 : ((DigitLower (pos)) < v)) (PreH17 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH18 : (0 <= (Znth 0 digits_2 0))) (PreH19 : ((Znth 0 digits_2 0) <= 9)) (PreH20 : (0 <= (Znth 1 digits_2 0))) (PreH21 : ((Znth 1 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 2 digits_2 0))) (PreH23 : ((Znth 2 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 3 digits_2 0))) (PreH25 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9)
.

Definition next_year_entail_wit_3_10_split_goal_6 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) > 2011)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH3 : (v <= 9)) (PreH4 : (1000 <= y_pre)) (PreH5 : (y_pre <= 9999)) (PreH6 : (1000 <= prev_pre)) (PreH7 : (prev_pre <= 2011)) (PreH8 : (0 <= pos)) (PreH9 : (pos < 4)) (PreH10 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH11 : ((DigitLower (pos)) <= v)) (PreH12 : (v <= 10)) (PreH13 : ((-1) <= best)) (PreH14 : (best <= 2011)) (PreH15 : (BestScanned y_pre prev_pre pos v best )) (PreH16 : ((DigitLower (pos)) < v)) (PreH17 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH18 : (0 <= (Znth 0 digits_2 0))) (PreH19 : ((Znth 0 digits_2 0) <= 9)) (PreH20 : (0 <= (Znth 1 digits_2 0))) (PreH21 : ((Znth 1 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 2 digits_2 0))) (PreH23 : ((Znth 2 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 3 digits_2 0))) (PreH25 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0))
.

Definition next_year_entail_wit_3_10_split_goal_7 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) > 2011)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH3 : (v <= 9)) (PreH4 : (1000 <= y_pre)) (PreH5 : (y_pre <= 9999)) (PreH6 : (1000 <= prev_pre)) (PreH7 : (prev_pre <= 2011)) (PreH8 : (0 <= pos)) (PreH9 : (pos < 4)) (PreH10 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH11 : ((DigitLower (pos)) <= v)) (PreH12 : (v <= 10)) (PreH13 : ((-1) <= best)) (PreH14 : (best <= 2011)) (PreH15 : (BestScanned y_pre prev_pre pos v best )) (PreH16 : ((DigitLower (pos)) < v)) (PreH17 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH18 : (0 <= (Znth 0 digits_2 0))) (PreH19 : ((Znth 0 digits_2 0) <= 9)) (PreH20 : (0 <= (Znth 1 digits_2 0))) (PreH21 : ((Znth 1 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 2 digits_2 0))) (PreH23 : ((Znth 2 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 3 digits_2 0))) (PreH25 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9)
.

Definition next_year_entail_wit_3_10_split_goal_8 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) > 2011)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH3 : (v <= 9)) (PreH4 : (1000 <= y_pre)) (PreH5 : (y_pre <= 9999)) (PreH6 : (1000 <= prev_pre)) (PreH7 : (prev_pre <= 2011)) (PreH8 : (0 <= pos)) (PreH9 : (pos < 4)) (PreH10 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH11 : ((DigitLower (pos)) <= v)) (PreH12 : (v <= 10)) (PreH13 : ((-1) <= best)) (PreH14 : (best <= 2011)) (PreH15 : (BestScanned y_pre prev_pre pos v best )) (PreH16 : ((DigitLower (pos)) < v)) (PreH17 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH18 : (0 <= (Znth 0 digits_2 0))) (PreH19 : ((Znth 0 digits_2 0) <= 9)) (PreH20 : (0 <= (Znth 1 digits_2 0))) (PreH21 : ((Znth 1 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 2 digits_2 0))) (PreH23 : ((Znth 2 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 3 digits_2 0))) (PreH25 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0))
.

Definition next_year_entail_wit_3_10_split_goal_9 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) > 2011)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH3 : (v <= 9)) (PreH4 : (1000 <= y_pre)) (PreH5 : (y_pre <= 9999)) (PreH6 : (1000 <= prev_pre)) (PreH7 : (prev_pre <= 2011)) (PreH8 : (0 <= pos)) (PreH9 : (pos < 4)) (PreH10 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH11 : ((DigitLower (pos)) <= v)) (PreH12 : (v <= 10)) (PreH13 : ((-1) <= best)) (PreH14 : (best <= 2011)) (PreH15 : (BestScanned y_pre prev_pre pos v best )) (PreH16 : ((DigitLower (pos)) < v)) (PreH17 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH18 : (0 <= (Znth 0 digits_2 0))) (PreH19 : ((Znth 0 digits_2 0) <= 9)) (PreH20 : (0 <= (Znth 1 digits_2 0))) (PreH21 : ((Znth 1 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 2 digits_2 0))) (PreH23 : ((Znth 2 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 3 digits_2 0))) (PreH25 : ((Znth 3 digits_2 0) <= 9)) ,
  (BestScanned y_pre prev_pre pos (v + 1 ) best )
.

Definition next_year_entail_wit_3_10_split_goal_10 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) > 2011)) (PreH2 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH3 : (v <= 9)) (PreH4 : (1000 <= y_pre)) (PreH5 : (y_pre <= 9999)) (PreH6 : (1000 <= prev_pre)) (PreH7 : (prev_pre <= 2011)) (PreH8 : (0 <= pos)) (PreH9 : (pos < 4)) (PreH10 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH11 : ((DigitLower (pos)) <= v)) (PreH12 : (v <= 10)) (PreH13 : ((-1) <= best)) (PreH14 : (best <= 2011)) (PreH15 : (BestScanned y_pre prev_pre pos v best )) (PreH16 : ((DigitLower (pos)) < v)) (PreH17 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH18 : (0 <= (Znth 0 digits_2 0))) (PreH19 : ((Znth 0 digits_2 0) <= 9)) (PreH20 : (0 <= (Znth 1 digits_2 0))) (PreH21 : ((Znth 1 digits_2 0) <= 9)) (PreH22 : (0 <= (Znth 2 digits_2 0))) (PreH23 : ((Znth 2 digits_2 0) <= 9)) (PreH24 : (0 <= (Znth 3 digits_2 0))) (PreH25 : ((Znth 3 digits_2 0) <= 9)) ,
  ((replace_Znth (pos) (v) (digits_2)) = (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))))
.

Definition next_year_entail_wit_3_11 := 
(
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : (v = (DigitLower (pos)))) (PreH20 : (digits_2 = (YearDigits (y_pre)))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits_2)) )
|--
  EX (digits: (@list Z)) ,
  “ (1000 <= y_pre) ” 
  &&  “ (y_pre <= 9999) ” 
  &&  “ (1000 <= prev_pre) ” 
  &&  “ (prev_pre <= 2011) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < 4) ” 
  &&  “ (old = (Znth pos (YearDigits (y_pre)) 0)) ” 
  &&  “ ((DigitLower (pos)) <= (v + 1 )) ” 
  &&  “ ((v + 1 ) <= 10) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 2011) ” 
  &&  “ (BestScanned y_pre prev_pre pos (v + 1 ) best ) ” 
  &&  “ ((DigitLower (pos)) < (v + 1 )) ” 
  &&  “ (digits = (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre))))) ” 
  &&  “ (0 <= (Znth 0 digits 0)) ” 
  &&  “ ((Znth 0 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 digits 0)) ” 
  &&  “ ((Znth 1 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 digits 0)) ” 
  &&  “ ((Znth 2 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 digits 0)) ” 
  &&  “ ((Znth 3 digits 0) <= 9) ”
  &&  (IntArray.full ( &( "d" ) ) 4 digits )
) \/
(
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : (v = (DigitLower (pos)))) (PreH20 : (digits_2 = (YearDigits (y_pre)))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  TT && emp 
|--
  “ ((Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0)) ” 
  &&  “ ((Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0)) ” 
  &&  “ ((Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0)) ” 
  &&  “ ((Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0)) ” 
  &&  “ (BestScanned y_pre prev_pre pos (v + 1 ) best ) ” 
  &&  “ ((replace_Znth (pos) (v) (digits_2)) = (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2))) ”
  &&  emp
).

Definition next_year_entail_wit_3_11_split_goal_1 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : (v = (DigitLower (pos)))) (PreH20 : (digits_2 = (YearDigits (y_pre)))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9)
.

Definition next_year_entail_wit_3_11_split_goal_2 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : (v = (DigitLower (pos)))) (PreH20 : (digits_2 = (YearDigits (y_pre)))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0))
.

Definition next_year_entail_wit_3_11_split_goal_3 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : (v = (DigitLower (pos)))) (PreH20 : (digits_2 = (YearDigits (y_pre)))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9)
.

Definition next_year_entail_wit_3_11_split_goal_4 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : (v = (DigitLower (pos)))) (PreH20 : (digits_2 = (YearDigits (y_pre)))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0))
.

Definition next_year_entail_wit_3_11_split_goal_5 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : (v = (DigitLower (pos)))) (PreH20 : (digits_2 = (YearDigits (y_pre)))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9)
.

Definition next_year_entail_wit_3_11_split_goal_6 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : (v = (DigitLower (pos)))) (PreH20 : (digits_2 = (YearDigits (y_pre)))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0))
.

Definition next_year_entail_wit_3_11_split_goal_7 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : (v = (DigitLower (pos)))) (PreH20 : (digits_2 = (YearDigits (y_pre)))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0) <= 9)
.

Definition next_year_entail_wit_3_11_split_goal_8 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : (v = (DigitLower (pos)))) (PreH20 : (digits_2 = (YearDigits (y_pre)))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)) 0))
.

Definition next_year_entail_wit_3_11_split_goal_9 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : (v = (DigitLower (pos)))) (PreH20 : (digits_2 = (YearDigits (y_pre)))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  (BestScanned y_pre prev_pre pos (v + 1 ) best )
.

Definition next_year_entail_wit_3_11_split_goal_10 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : (v = (DigitLower (pos)))) (PreH20 : (digits_2 = (YearDigits (y_pre)))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  ((replace_Znth (pos) (v) (digits_2)) = (replace_Znth (pos) (((v + 1 ) - 1 )) (digits_2)))
.

Definition next_year_entail_wit_3_12 := 
(
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : ((DigitLower (pos)) < v)) (PreH20 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits_2)) )
|--
  EX (digits: (@list Z)) ,
  “ (1000 <= y_pre) ” 
  &&  “ (y_pre <= 9999) ” 
  &&  “ (1000 <= prev_pre) ” 
  &&  “ (prev_pre <= 2011) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < 4) ” 
  &&  “ (old = (Znth pos (YearDigits (y_pre)) 0)) ” 
  &&  “ ((DigitLower (pos)) <= (v + 1 )) ” 
  &&  “ ((v + 1 ) <= 10) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 2011) ” 
  &&  “ (BestScanned y_pre prev_pre pos (v + 1 ) best ) ” 
  &&  “ ((DigitLower (pos)) < (v + 1 )) ” 
  &&  “ (digits = (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre))))) ” 
  &&  “ (0 <= (Znth 0 digits 0)) ” 
  &&  “ ((Znth 0 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 digits 0)) ” 
  &&  “ ((Znth 1 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 digits 0)) ” 
  &&  “ ((Znth 2 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 digits 0)) ” 
  &&  “ ((Znth 3 digits 0) <= 9) ”
  &&  (IntArray.full ( &( "d" ) ) 4 digits )
) \/
(
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : ((DigitLower (pos)) < v)) (PreH20 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  TT && emp 
|--
  “ ((Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0)) ” 
  &&  “ ((Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0)) ” 
  &&  “ ((Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0)) ” 
  &&  “ ((Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9) ” 
  &&  “ (0 <= (Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0)) ” 
  &&  “ (BestScanned y_pre prev_pre pos (v + 1 ) best ) ” 
  &&  “ ((replace_Znth (pos) (v) (digits_2)) = (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre))))) ”
  &&  emp
).

Definition next_year_entail_wit_3_12_split_goal_1 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : ((DigitLower (pos)) < v)) (PreH20 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9)
.

Definition next_year_entail_wit_3_12_split_goal_2 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : ((DigitLower (pos)) < v)) (PreH20 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 3 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0))
.

Definition next_year_entail_wit_3_12_split_goal_3 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : ((DigitLower (pos)) < v)) (PreH20 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9)
.

Definition next_year_entail_wit_3_12_split_goal_4 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : ((DigitLower (pos)) < v)) (PreH20 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 2 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0))
.

Definition next_year_entail_wit_3_12_split_goal_5 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : ((DigitLower (pos)) < v)) (PreH20 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9)
.

Definition next_year_entail_wit_3_12_split_goal_6 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : ((DigitLower (pos)) < v)) (PreH20 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 1 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0))
.

Definition next_year_entail_wit_3_12_split_goal_7 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : ((DigitLower (pos)) < v)) (PreH20 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  ((Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0) <= 9)
.

Definition next_year_entail_wit_3_12_split_goal_8 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : ((DigitLower (pos)) < v)) (PreH20 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  (0 <= (Znth 0 (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))) 0))
.

Definition next_year_entail_wit_3_12_split_goal_9 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : ((DigitLower (pos)) < v)) (PreH20 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  (BestScanned y_pre prev_pre pos (v + 1 ) best )
.

Definition next_year_entail_wit_3_12_split_goal_10 := 
forall (prev_pre: Z) (y_pre: Z) (digits_2: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= best)) (PreH2 : (best >= 0)) (PreH3 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= prev_pre)) (PreH4 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) <= 2011)) (PreH5 : ((((((Znth 0 (replace_Znth (pos) (v) (digits_2)) 0) * 1000 ) + ((Znth 1 (replace_Znth (pos) (v) (digits_2)) 0) * 100 ) ) + ((Znth 2 (replace_Znth (pos) (v) (digits_2)) 0) * 10 ) ) + (Znth 3 (replace_Znth (pos) (v) (digits_2)) 0) ) >= 1000)) (PreH6 : (v <= 9)) (PreH7 : (1000 <= y_pre)) (PreH8 : (y_pre <= 9999)) (PreH9 : (1000 <= prev_pre)) (PreH10 : (prev_pre <= 2011)) (PreH11 : (0 <= pos)) (PreH12 : (pos < 4)) (PreH13 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH14 : ((DigitLower (pos)) <= v)) (PreH15 : (v <= 10)) (PreH16 : ((-1) <= best)) (PreH17 : (best <= 2011)) (PreH18 : (BestScanned y_pre prev_pre pos v best )) (PreH19 : ((DigitLower (pos)) < v)) (PreH20 : (digits_2 = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH21 : (0 <= (Znth 0 digits_2 0))) (PreH22 : ((Znth 0 digits_2 0) <= 9)) (PreH23 : (0 <= (Znth 1 digits_2 0))) (PreH24 : ((Znth 1 digits_2 0) <= 9)) (PreH25 : (0 <= (Znth 2 digits_2 0))) (PreH26 : ((Znth 2 digits_2 0) <= 9)) (PreH27 : (0 <= (Znth 3 digits_2 0))) (PreH28 : ((Znth 3 digits_2 0) <= 9)) ,
  ((replace_Znth (pos) (v) (digits_2)) = (replace_Znth (pos) (((v + 1 ) - 1 )) ((YearDigits (y_pre)))))
.

Definition next_year_entail_wit_4_1 := 
(
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v > 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (old) (digits)) )
|--
  “ (1000 <= y_pre) ” 
  &&  “ (y_pre <= 9999) ” 
  &&  “ (1000 <= prev_pre) ” 
  &&  “ (prev_pre <= 2011) ” 
  &&  “ (0 <= (pos + 1 )) ” 
  &&  “ ((pos + 1 ) <= 4) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 2011) ” 
  &&  “ (BestScanned y_pre prev_pre (pos + 1 ) (DigitLower ((pos + 1 ))) best ) ” 
  &&  “ (0 <= (Znth 0 (YearDigits (y_pre)) 0)) ” 
  &&  “ ((Znth 0 (YearDigits (y_pre)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 (YearDigits (y_pre)) 0)) ” 
  &&  “ ((Znth 1 (YearDigits (y_pre)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 (YearDigits (y_pre)) 0)) ” 
  &&  “ ((Znth 2 (YearDigits (y_pre)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 (YearDigits (y_pre)) 0)) ” 
  &&  “ ((Znth 3 (YearDigits (y_pre)) 0) <= 9) ”
  &&  (IntArray.full ( &( "d" ) ) 4 (YearDigits (y_pre)) )
) \/
(
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v > 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  TT && emp 
|--
  “ (BestScanned y_pre prev_pre (pos + 1 ) (DigitLower ((pos + 1 ))) best ) ” 
  &&  “ ((replace_Znth (pos) (old) (digits)) = digits) ”
  &&  emp
).

Definition next_year_entail_wit_4_1_split_goal_1 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v > 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (BestScanned y_pre prev_pre (pos + 1 ) (DigitLower ((pos + 1 ))) best )
.

Definition next_year_entail_wit_4_1_split_goal_2 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v > 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  ((replace_Znth (pos) (old) (digits)) = digits)
.

Definition next_year_entail_wit_4_2 := 
(
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v > 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (old) (digits)) )
|--
  “ (1000 <= y_pre) ” 
  &&  “ (y_pre <= 9999) ” 
  &&  “ (1000 <= prev_pre) ” 
  &&  “ (prev_pre <= 2011) ” 
  &&  “ (0 <= (pos + 1 )) ” 
  &&  “ ((pos + 1 ) <= 4) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 2011) ” 
  &&  “ (BestScanned y_pre prev_pre (pos + 1 ) (DigitLower ((pos + 1 ))) best ) ” 
  &&  “ (0 <= (Znth 0 (YearDigits (y_pre)) 0)) ” 
  &&  “ ((Znth 0 (YearDigits (y_pre)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 (YearDigits (y_pre)) 0)) ” 
  &&  “ ((Znth 1 (YearDigits (y_pre)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 (YearDigits (y_pre)) 0)) ” 
  &&  “ ((Znth 2 (YearDigits (y_pre)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 (YearDigits (y_pre)) 0)) ” 
  &&  “ ((Znth 3 (YearDigits (y_pre)) 0) <= 9) ”
  &&  (IntArray.full ( &( "d" ) ) 4 (YearDigits (y_pre)) )
) \/
(
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v > 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  TT && emp 
|--
  “ ((Znth 3 (YearDigits (y_pre)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 (YearDigits (y_pre)) 0)) ” 
  &&  “ ((Znth 2 (YearDigits (y_pre)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 (YearDigits (y_pre)) 0)) ” 
  &&  “ ((Znth 1 (YearDigits (y_pre)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 (YearDigits (y_pre)) 0)) ” 
  &&  “ ((Znth 0 (YearDigits (y_pre)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 0 (YearDigits (y_pre)) 0)) ” 
  &&  “ (BestScanned y_pre prev_pre (pos + 1 ) (DigitLower ((pos + 1 ))) best ) ” 
  &&  “ ((replace_Znth (pos) (old) (digits)) = (YearDigits (y_pre))) ”
  &&  emp
).

Definition next_year_entail_wit_4_2_split_goal_1 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v > 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  ((Znth 3 (YearDigits (y_pre)) 0) <= 9)
.

Definition next_year_entail_wit_4_2_split_goal_2 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v > 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (0 <= (Znth 3 (YearDigits (y_pre)) 0))
.

Definition next_year_entail_wit_4_2_split_goal_3 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v > 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  ((Znth 2 (YearDigits (y_pre)) 0) <= 9)
.

Definition next_year_entail_wit_4_2_split_goal_4 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v > 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (0 <= (Znth 2 (YearDigits (y_pre)) 0))
.

Definition next_year_entail_wit_4_2_split_goal_5 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v > 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  ((Znth 1 (YearDigits (y_pre)) 0) <= 9)
.

Definition next_year_entail_wit_4_2_split_goal_6 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v > 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (0 <= (Znth 1 (YearDigits (y_pre)) 0))
.

Definition next_year_entail_wit_4_2_split_goal_7 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v > 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  ((Znth 0 (YearDigits (y_pre)) 0) <= 9)
.

Definition next_year_entail_wit_4_2_split_goal_8 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v > 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (0 <= (Znth 0 (YearDigits (y_pre)) 0))
.

Definition next_year_entail_wit_4_2_split_goal_9 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v > 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (BestScanned y_pre prev_pre (pos + 1 ) (DigitLower ((pos + 1 ))) best )
.

Definition next_year_entail_wit_4_2_split_goal_10 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v > 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  ((replace_Znth (pos) (old) (digits)) = (YearDigits (y_pre)))
.

Definition next_year_return_wit_1 := 
(
forall (prev_pre: Z) (y_pre: Z) (best: Z) (pos: Z) (PreH1 : (pos >= 4)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos <= 4)) (PreH8 : ((-1) <= best)) (PreH9 : (best <= 2011)) (PreH10 : (BestScanned y_pre prev_pre pos (DigitLower (pos)) best )) (PreH11 : (0 <= (Znth 0 (YearDigits (y_pre)) 0))) (PreH12 : ((Znth 0 (YearDigits (y_pre)) 0) <= 9)) (PreH13 : (0 <= (Znth 1 (YearDigits (y_pre)) 0))) (PreH14 : ((Znth 1 (YearDigits (y_pre)) 0) <= 9)) (PreH15 : (0 <= (Znth 2 (YearDigits (y_pre)) 0))) (PreH16 : ((Znth 2 (YearDigits (y_pre)) 0) <= 9)) (PreH17 : (0 <= (Znth 3 (YearDigits (y_pre)) 0))) (PreH18 : ((Znth 3 (YearDigits (y_pre)) 0) <= 9)) ,
  TT && emp 
|--
  “ (NextYearResult y_pre prev_pre best ) ”
  &&  emp
) \/
(
forall (prev_pre: Z) (y_pre: Z) (best: Z) (pos: Z) (PreH1 : (pos >= 4)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos <= 4)) (PreH8 : ((-1) <= best)) (PreH9 : (best <= 2011)) (PreH10 : (BestScanned y_pre prev_pre pos (DigitLower (pos)) best )) (PreH11 : (0 <= (Znth 0 (YearDigits (y_pre)) 0))) (PreH12 : ((Znth 0 (YearDigits (y_pre)) 0) <= 9)) (PreH13 : (0 <= (Znth 1 (YearDigits (y_pre)) 0))) (PreH14 : ((Znth 1 (YearDigits (y_pre)) 0) <= 9)) (PreH15 : (0 <= (Znth 2 (YearDigits (y_pre)) 0))) (PreH16 : ((Znth 2 (YearDigits (y_pre)) 0) <= 9)) (PreH17 : (0 <= (Znth 3 (YearDigits (y_pre)) 0))) (PreH18 : ((Znth 3 (YearDigits (y_pre)) 0) <= 9)) ,
  TT && emp 
|--
  “ (NextYearResult y_pre prev_pre best ) ”
  &&  emp
).

Definition next_year_return_wit_1_split_goal_1 := 
forall (prev_pre: Z) (y_pre: Z) (best: Z) (pos: Z) (PreH1 : (pos >= 4)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos <= 4)) (PreH8 : ((-1) <= best)) (PreH9 : (best <= 2011)) (PreH10 : (BestScanned y_pre prev_pre pos (DigitLower (pos)) best )) (PreH11 : (0 <= (Znth 0 (YearDigits (y_pre)) 0))) (PreH12 : ((Znth 0 (YearDigits (y_pre)) 0) <= 9)) (PreH13 : (0 <= (Znth 1 (YearDigits (y_pre)) 0))) (PreH14 : ((Znth 1 (YearDigits (y_pre)) 0) <= 9)) (PreH15 : (0 <= (Znth 2 (YearDigits (y_pre)) 0))) (PreH16 : ((Znth 2 (YearDigits (y_pre)) 0) <= 9)) (PreH17 : (0 <= (Znth 3 (YearDigits (y_pre)) 0))) (PreH18 : ((Znth 3 (YearDigits (y_pre)) 0) <= 9)) ,
  (NextYearResult y_pre prev_pre best )
.

Definition next_year_partial_solve_wit_1 := 
forall (prev_pre: Z) (y_pre: Z) (best: Z) (pos: Z) (PreH1 : (pos < 4)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos <= 4)) (PreH8 : ((-1) <= best)) (PreH9 : (best <= 2011)) (PreH10 : (BestScanned y_pre prev_pre pos (DigitLower (pos)) best )) (PreH11 : (0 <= (Znth 0 (YearDigits (y_pre)) 0))) (PreH12 : ((Znth 0 (YearDigits (y_pre)) 0) <= 9)) (PreH13 : (0 <= (Znth 1 (YearDigits (y_pre)) 0))) (PreH14 : ((Znth 1 (YearDigits (y_pre)) 0) <= 9)) (PreH15 : (0 <= (Znth 2 (YearDigits (y_pre)) 0))) (PreH16 : ((Znth 2 (YearDigits (y_pre)) 0) <= 9)) (PreH17 : (0 <= (Znth 3 (YearDigits (y_pre)) 0))) (PreH18 : ((Znth 3 (YearDigits (y_pre)) 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (YearDigits (y_pre)) )
|--
  “ (pos < 4) ” 
  &&  “ (1000 <= y_pre) ” 
  &&  “ (y_pre <= 9999) ” 
  &&  “ (1000 <= prev_pre) ” 
  &&  “ (prev_pre <= 2011) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= 4) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 2011) ” 
  &&  “ (BestScanned y_pre prev_pre pos (DigitLower (pos)) best ) ” 
  &&  “ (0 <= (Znth 0 (YearDigits (y_pre)) 0)) ” 
  &&  “ ((Znth 0 (YearDigits (y_pre)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 (YearDigits (y_pre)) 0)) ” 
  &&  “ ((Znth 1 (YearDigits (y_pre)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 (YearDigits (y_pre)) 0)) ” 
  &&  “ ((Znth 2 (YearDigits (y_pre)) 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 (YearDigits (y_pre)) 0)) ” 
  &&  “ ((Znth 3 (YearDigits (y_pre)) 0) <= 9) ”
  &&  (((( &( "d" ) ) + (pos * sizeof(INT)))) # Int  |-> (Znth pos (YearDigits (y_pre)) 0))
  **  (IntArray.missing_i ( &( "d" ) ) pos 0 4 (YearDigits (y_pre)) )
.

Definition next_year_partial_solve_wit_2 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 digits )
|--
  “ (v <= 9) ” 
  &&  “ (1000 <= y_pre) ” 
  &&  “ (y_pre <= 9999) ” 
  &&  “ (1000 <= prev_pre) ” 
  &&  “ (prev_pre <= 2011) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < 4) ” 
  &&  “ (old = (Znth pos (YearDigits (y_pre)) 0)) ” 
  &&  “ ((DigitLower (pos)) <= v) ” 
  &&  “ (v <= 10) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 2011) ” 
  &&  “ (BestScanned y_pre prev_pre pos v best ) ” 
  &&  “ (v = (DigitLower (pos))) ” 
  &&  “ (digits = (YearDigits (y_pre))) ” 
  &&  “ (0 <= (Znth 0 digits 0)) ” 
  &&  “ ((Znth 0 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 digits 0)) ” 
  &&  “ ((Znth 1 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 digits 0)) ” 
  &&  “ ((Znth 2 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 digits 0)) ” 
  &&  “ ((Znth 3 digits 0) <= 9) ”
  &&  (((( &( "d" ) ) + (pos * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "d" ) ) pos 0 4 digits )
.

Definition next_year_partial_solve_wit_3 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 digits )
|--
  “ (v <= 9) ” 
  &&  “ (1000 <= y_pre) ” 
  &&  “ (y_pre <= 9999) ” 
  &&  “ (1000 <= prev_pre) ” 
  &&  “ (prev_pre <= 2011) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < 4) ” 
  &&  “ (old = (Znth pos (YearDigits (y_pre)) 0)) ” 
  &&  “ ((DigitLower (pos)) <= v) ” 
  &&  “ (v <= 10) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 2011) ” 
  &&  “ (BestScanned y_pre prev_pre pos v best ) ” 
  &&  “ ((DigitLower (pos)) < v) ” 
  &&  “ (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre))))) ” 
  &&  “ (0 <= (Znth 0 digits 0)) ” 
  &&  “ ((Znth 0 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 digits 0)) ” 
  &&  “ ((Znth 1 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 digits 0)) ” 
  &&  “ ((Znth 2 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 digits 0)) ” 
  &&  “ ((Znth 3 digits 0) <= 9) ”
  &&  (((( &( "d" ) ) + (pos * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "d" ) ) pos 0 4 digits )
.

Definition next_year_partial_solve_wit_4 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
|--
  “ (v <= 9) ” 
  &&  “ (1000 <= y_pre) ” 
  &&  “ (y_pre <= 9999) ” 
  &&  “ (1000 <= prev_pre) ” 
  &&  “ (prev_pre <= 2011) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < 4) ” 
  &&  “ (old = (Znth pos (YearDigits (y_pre)) 0)) ” 
  &&  “ ((DigitLower (pos)) <= v) ” 
  &&  “ (v <= 10) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 2011) ” 
  &&  “ (BestScanned y_pre prev_pre pos v best ) ” 
  &&  “ (v = (DigitLower (pos))) ” 
  &&  “ (digits = (YearDigits (y_pre))) ” 
  &&  “ (0 <= (Znth 0 digits 0)) ” 
  &&  “ ((Znth 0 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 digits 0)) ” 
  &&  “ ((Znth 1 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 digits 0)) ” 
  &&  “ ((Znth 2 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 digits 0)) ” 
  &&  “ ((Znth 3 digits 0) <= 9) ”
  &&  (((( &( "d" ) ) + (0 * sizeof(INT)))) # Int  |-> (Znth 0 (replace_Znth (pos) (v) (digits)) 0))
  **  (IntArray.missing_i ( &( "d" ) ) 0 0 4 (replace_Znth (pos) (v) (digits)) )
.

Definition next_year_partial_solve_wit_5 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
|--
  “ (v <= 9) ” 
  &&  “ (1000 <= y_pre) ” 
  &&  “ (y_pre <= 9999) ” 
  &&  “ (1000 <= prev_pre) ” 
  &&  “ (prev_pre <= 2011) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < 4) ” 
  &&  “ (old = (Znth pos (YearDigits (y_pre)) 0)) ” 
  &&  “ ((DigitLower (pos)) <= v) ” 
  &&  “ (v <= 10) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 2011) ” 
  &&  “ (BestScanned y_pre prev_pre pos v best ) ” 
  &&  “ (v = (DigitLower (pos))) ” 
  &&  “ (digits = (YearDigits (y_pre))) ” 
  &&  “ (0 <= (Znth 0 digits 0)) ” 
  &&  “ ((Znth 0 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 digits 0)) ” 
  &&  “ ((Znth 1 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 digits 0)) ” 
  &&  “ ((Znth 2 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 digits 0)) ” 
  &&  “ ((Znth 3 digits 0) <= 9) ”
  &&  (((( &( "d" ) ) + (1 * sizeof(INT)))) # Int  |-> (Znth 1 (replace_Znth (pos) (v) (digits)) 0))
  **  (IntArray.missing_i ( &( "d" ) ) 1 0 4 (replace_Znth (pos) (v) (digits)) )
.

Definition next_year_partial_solve_wit_6 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
|--
  “ (v <= 9) ” 
  &&  “ (1000 <= y_pre) ” 
  &&  “ (y_pre <= 9999) ” 
  &&  “ (1000 <= prev_pre) ” 
  &&  “ (prev_pre <= 2011) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < 4) ” 
  &&  “ (old = (Znth pos (YearDigits (y_pre)) 0)) ” 
  &&  “ ((DigitLower (pos)) <= v) ” 
  &&  “ (v <= 10) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 2011) ” 
  &&  “ (BestScanned y_pre prev_pre pos v best ) ” 
  &&  “ (v = (DigitLower (pos))) ” 
  &&  “ (digits = (YearDigits (y_pre))) ” 
  &&  “ (0 <= (Znth 0 digits 0)) ” 
  &&  “ ((Znth 0 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 digits 0)) ” 
  &&  “ ((Znth 1 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 digits 0)) ” 
  &&  “ ((Znth 2 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 digits 0)) ” 
  &&  “ ((Znth 3 digits 0) <= 9) ”
  &&  (((( &( "d" ) ) + (2 * sizeof(INT)))) # Int  |-> (Znth 2 (replace_Znth (pos) (v) (digits)) 0))
  **  (IntArray.missing_i ( &( "d" ) ) 2 0 4 (replace_Znth (pos) (v) (digits)) )
.

Definition next_year_partial_solve_wit_7 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
|--
  “ (v <= 9) ” 
  &&  “ (1000 <= y_pre) ” 
  &&  “ (y_pre <= 9999) ” 
  &&  “ (1000 <= prev_pre) ” 
  &&  “ (prev_pre <= 2011) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < 4) ” 
  &&  “ (old = (Znth pos (YearDigits (y_pre)) 0)) ” 
  &&  “ ((DigitLower (pos)) <= v) ” 
  &&  “ (v <= 10) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 2011) ” 
  &&  “ (BestScanned y_pre prev_pre pos v best ) ” 
  &&  “ (v = (DigitLower (pos))) ” 
  &&  “ (digits = (YearDigits (y_pre))) ” 
  &&  “ (0 <= (Znth 0 digits 0)) ” 
  &&  “ ((Znth 0 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 digits 0)) ” 
  &&  “ ((Znth 1 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 digits 0)) ” 
  &&  “ ((Znth 2 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 digits 0)) ” 
  &&  “ ((Znth 3 digits 0) <= 9) ”
  &&  (((( &( "d" ) ) + (3 * sizeof(INT)))) # Int  |-> (Znth 3 (replace_Znth (pos) (v) (digits)) 0))
  **  (IntArray.missing_i ( &( "d" ) ) 3 0 4 (replace_Znth (pos) (v) (digits)) )
.

Definition next_year_partial_solve_wit_8 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
|--
  “ (v <= 9) ” 
  &&  “ (1000 <= y_pre) ” 
  &&  “ (y_pre <= 9999) ” 
  &&  “ (1000 <= prev_pre) ” 
  &&  “ (prev_pre <= 2011) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < 4) ” 
  &&  “ (old = (Znth pos (YearDigits (y_pre)) 0)) ” 
  &&  “ ((DigitLower (pos)) <= v) ” 
  &&  “ (v <= 10) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 2011) ” 
  &&  “ (BestScanned y_pre prev_pre pos v best ) ” 
  &&  “ ((DigitLower (pos)) < v) ” 
  &&  “ (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre))))) ” 
  &&  “ (0 <= (Znth 0 digits 0)) ” 
  &&  “ ((Znth 0 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 digits 0)) ” 
  &&  “ ((Znth 1 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 digits 0)) ” 
  &&  “ ((Znth 2 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 digits 0)) ” 
  &&  “ ((Znth 3 digits 0) <= 9) ”
  &&  (((( &( "d" ) ) + (0 * sizeof(INT)))) # Int  |-> (Znth 0 (replace_Znth (pos) (v) (digits)) 0))
  **  (IntArray.missing_i ( &( "d" ) ) 0 0 4 (replace_Znth (pos) (v) (digits)) )
.

Definition next_year_partial_solve_wit_9 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
|--
  “ (v <= 9) ” 
  &&  “ (1000 <= y_pre) ” 
  &&  “ (y_pre <= 9999) ” 
  &&  “ (1000 <= prev_pre) ” 
  &&  “ (prev_pre <= 2011) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < 4) ” 
  &&  “ (old = (Znth pos (YearDigits (y_pre)) 0)) ” 
  &&  “ ((DigitLower (pos)) <= v) ” 
  &&  “ (v <= 10) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 2011) ” 
  &&  “ (BestScanned y_pre prev_pre pos v best ) ” 
  &&  “ ((DigitLower (pos)) < v) ” 
  &&  “ (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre))))) ” 
  &&  “ (0 <= (Znth 0 digits 0)) ” 
  &&  “ ((Znth 0 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 digits 0)) ” 
  &&  “ ((Znth 1 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 digits 0)) ” 
  &&  “ ((Znth 2 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 digits 0)) ” 
  &&  “ ((Znth 3 digits 0) <= 9) ”
  &&  (((( &( "d" ) ) + (1 * sizeof(INT)))) # Int  |-> (Znth 1 (replace_Znth (pos) (v) (digits)) 0))
  **  (IntArray.missing_i ( &( "d" ) ) 1 0 4 (replace_Znth (pos) (v) (digits)) )
.

Definition next_year_partial_solve_wit_10 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
|--
  “ (v <= 9) ” 
  &&  “ (1000 <= y_pre) ” 
  &&  “ (y_pre <= 9999) ” 
  &&  “ (1000 <= prev_pre) ” 
  &&  “ (prev_pre <= 2011) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < 4) ” 
  &&  “ (old = (Znth pos (YearDigits (y_pre)) 0)) ” 
  &&  “ ((DigitLower (pos)) <= v) ” 
  &&  “ (v <= 10) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 2011) ” 
  &&  “ (BestScanned y_pre prev_pre pos v best ) ” 
  &&  “ ((DigitLower (pos)) < v) ” 
  &&  “ (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre))))) ” 
  &&  “ (0 <= (Znth 0 digits 0)) ” 
  &&  “ ((Znth 0 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 digits 0)) ” 
  &&  “ ((Znth 1 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 digits 0)) ” 
  &&  “ ((Znth 2 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 digits 0)) ” 
  &&  “ ((Znth 3 digits 0) <= 9) ”
  &&  (((( &( "d" ) ) + (2 * sizeof(INT)))) # Int  |-> (Znth 2 (replace_Znth (pos) (v) (digits)) 0))
  **  (IntArray.missing_i ( &( "d" ) ) 2 0 4 (replace_Znth (pos) (v) (digits)) )
.

Definition next_year_partial_solve_wit_11 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v <= 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 (replace_Znth (pos) (v) (digits)) )
|--
  “ (v <= 9) ” 
  &&  “ (1000 <= y_pre) ” 
  &&  “ (y_pre <= 9999) ” 
  &&  “ (1000 <= prev_pre) ” 
  &&  “ (prev_pre <= 2011) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < 4) ” 
  &&  “ (old = (Znth pos (YearDigits (y_pre)) 0)) ” 
  &&  “ ((DigitLower (pos)) <= v) ” 
  &&  “ (v <= 10) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 2011) ” 
  &&  “ (BestScanned y_pre prev_pre pos v best ) ” 
  &&  “ ((DigitLower (pos)) < v) ” 
  &&  “ (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre))))) ” 
  &&  “ (0 <= (Znth 0 digits 0)) ” 
  &&  “ ((Znth 0 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 digits 0)) ” 
  &&  “ ((Znth 1 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 digits 0)) ” 
  &&  “ ((Znth 2 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 digits 0)) ” 
  &&  “ ((Znth 3 digits 0) <= 9) ”
  &&  (((( &( "d" ) ) + (3 * sizeof(INT)))) # Int  |-> (Znth 3 (replace_Znth (pos) (v) (digits)) 0))
  **  (IntArray.missing_i ( &( "d" ) ) 3 0 4 (replace_Znth (pos) (v) (digits)) )
.

Definition next_year_partial_solve_wit_12 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v > 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : (v = (DigitLower (pos)))) (PreH15 : (digits = (YearDigits (y_pre)))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 digits )
|--
  “ (v > 9) ” 
  &&  “ (1000 <= y_pre) ” 
  &&  “ (y_pre <= 9999) ” 
  &&  “ (1000 <= prev_pre) ” 
  &&  “ (prev_pre <= 2011) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < 4) ” 
  &&  “ (old = (Znth pos (YearDigits (y_pre)) 0)) ” 
  &&  “ ((DigitLower (pos)) <= v) ” 
  &&  “ (v <= 10) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 2011) ” 
  &&  “ (BestScanned y_pre prev_pre pos v best ) ” 
  &&  “ (v = (DigitLower (pos))) ” 
  &&  “ (digits = (YearDigits (y_pre))) ” 
  &&  “ (0 <= (Znth 0 digits 0)) ” 
  &&  “ ((Znth 0 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 digits 0)) ” 
  &&  “ ((Znth 1 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 digits 0)) ” 
  &&  “ ((Znth 2 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 digits 0)) ” 
  &&  “ ((Znth 3 digits 0) <= 9) ”
  &&  (((( &( "d" ) ) + (pos * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "d" ) ) pos 0 4 digits )
.

Definition next_year_partial_solve_wit_13 := 
forall (prev_pre: Z) (y_pre: Z) (digits: (@list Z)) (best: Z) (v: Z) (old: Z) (pos: Z) (PreH1 : (v > 9)) (PreH2 : (1000 <= y_pre)) (PreH3 : (y_pre <= 9999)) (PreH4 : (1000 <= prev_pre)) (PreH5 : (prev_pre <= 2011)) (PreH6 : (0 <= pos)) (PreH7 : (pos < 4)) (PreH8 : (old = (Znth pos (YearDigits (y_pre)) 0))) (PreH9 : ((DigitLower (pos)) <= v)) (PreH10 : (v <= 10)) (PreH11 : ((-1) <= best)) (PreH12 : (best <= 2011)) (PreH13 : (BestScanned y_pre prev_pre pos v best )) (PreH14 : ((DigitLower (pos)) < v)) (PreH15 : (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre)))))) (PreH16 : (0 <= (Znth 0 digits 0))) (PreH17 : ((Znth 0 digits 0) <= 9)) (PreH18 : (0 <= (Znth 1 digits 0))) (PreH19 : ((Znth 1 digits 0) <= 9)) (PreH20 : (0 <= (Znth 2 digits 0))) (PreH21 : ((Znth 2 digits 0) <= 9)) (PreH22 : (0 <= (Znth 3 digits 0))) (PreH23 : ((Znth 3 digits 0) <= 9)) ,
  (IntArray.full ( &( "d" ) ) 4 digits )
|--
  “ (v > 9) ” 
  &&  “ (1000 <= y_pre) ” 
  &&  “ (y_pre <= 9999) ” 
  &&  “ (1000 <= prev_pre) ” 
  &&  “ (prev_pre <= 2011) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < 4) ” 
  &&  “ (old = (Znth pos (YearDigits (y_pre)) 0)) ” 
  &&  “ ((DigitLower (pos)) <= v) ” 
  &&  “ (v <= 10) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 2011) ” 
  &&  “ (BestScanned y_pre prev_pre pos v best ) ” 
  &&  “ ((DigitLower (pos)) < v) ” 
  &&  “ (digits = (replace_Znth (pos) ((v - 1 )) ((YearDigits (y_pre))))) ” 
  &&  “ (0 <= (Znth 0 digits 0)) ” 
  &&  “ ((Znth 0 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 1 digits 0)) ” 
  &&  “ ((Znth 1 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 2 digits 0)) ” 
  &&  “ ((Znth 2 digits 0) <= 9) ” 
  &&  “ (0 <= (Znth 3 digits 0)) ” 
  &&  “ ((Znth 3 digits 0) <= 9) ”
  &&  (((( &( "d" ) ) + (pos * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "d" ) ) pos 0 4 digits )
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (out_pre: Z) (n_pre: Z) (years_pre: Z) (input_years: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1000 <= (Znth i input_years 0)) /\ ((Znth i input_years 0) <= 9999)))) (PreH4 : (n_pre = (Zlength (input_years)))) ,
  ((( &( "prev" ) )) # Int  |->_)
  **  ((( &( "years" ) )) # Ptr  |-> years_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full years_pre n_pre input_years )
  **  (IntArray.full_shape out_pre n_pre )
|--
  “ (1000 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1000) ”
.

Definition solver_safety_wit_2 := 
forall (out_pre: Z) (n_pre: Z) (years_pre: Z) (input_years: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1000 <= (Znth i input_years 0)) /\ ((Znth i input_years 0) <= 9999)))) (PreH4 : (n_pre = (Zlength (input_years)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "prev" ) )) # Int  |-> 1000)
  **  ((( &( "years" ) )) # Ptr  |-> years_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full years_pre n_pre input_years )
  **  (IntArray.full_shape out_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 := 
forall (out_pre: Z) (n_pre: Z) (years_pre: Z) (input_years: (@list Z)) (done: (@list Z)) (old_out: Z) (i: Z) (prev: Z) (retval: Z) (PreH1 : (NextYearResult (Znth i input_years 0) prev retval )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (input_years)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1000 <= (Znth k input_years 0)) /\ ((Znth k input_years 0) <= 9999)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (i = (Zlength (done)))) (PreH9 : (prev = (PreviousYear (done)))) (PreH10 : (GreedyPrefix input_years done )) ,
  (IntArray.full out_pre (i + 1 ) (replace_Znth (i) (retval) ((app (done) ((cons (old_out) ((@nil Z))))))) )
  **  (IntArray.full years_pre n_pre input_years )
  **  ((( &( "years" ) )) # Ptr  |-> years_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "prev" ) )) # Int  |-> prev)
  **  (IntArray.missing_i_shape out_pre i i n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 := 
forall (out_pre: Z) (n_pre: Z) (years_pre: Z) (input_years: (@list Z)) (done: (@list Z)) (old_out: Z) (i: Z) (prev: Z) (retval: Z) (PreH1 : ((Znth i (replace_Znth (i) (retval) ((app (done) ((cons (old_out) ((@nil Z))))))) 0) < 0)) (PreH2 : (NextYearResult (Znth i input_years 0) prev retval )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (n_pre = (Zlength (input_years)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1000 <= (Znth k input_years 0)) /\ ((Znth k input_years 0) <= 9999)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (i = (Zlength (done)))) (PreH10 : (prev = (PreviousYear (done)))) (PreH11 : (GreedyPrefix input_years done )) ,
  (IntArray.full out_pre (i + 1 ) (replace_Znth (i) (retval) ((app (done) ((cons (old_out) ((@nil Z))))))) )
  **  (IntArray.full years_pre n_pre input_years )
  **  ((( &( "years" ) )) # Ptr  |-> years_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "prev" ) )) # Int  |-> prev)
  **  (IntArray.missing_i_shape out_pre i i n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_5 := 
forall (out_pre: Z) (n_pre: Z) (years_pre: Z) (input_years: (@list Z)) (done: (@list Z)) (old_out: Z) (i: Z) (prev: Z) (retval: Z) (PreH1 : ((Znth i (replace_Znth (i) (retval) ((app (done) ((cons (old_out) ((@nil Z))))))) 0) >= 0)) (PreH2 : (NextYearResult (Znth i input_years 0) prev retval )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (n_pre = (Zlength (input_years)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1000 <= (Znth k input_years 0)) /\ ((Znth k input_years 0) <= 9999)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (i = (Zlength (done)))) (PreH10 : (prev = (PreviousYear (done)))) (PreH11 : (GreedyPrefix input_years done )) ,
  (IntArray.full out_pre (i + 1 ) (replace_Znth (i) (retval) ((app (done) ((cons (old_out) ((@nil Z))))))) )
  **  (IntArray.full years_pre n_pre input_years )
  **  ((( &( "years" ) )) # Ptr  |-> years_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "prev" ) )) # Int  |-> (Znth i (replace_Znth (i) (retval) ((app (done) ((cons (old_out) ((@nil Z))))))) 0))
  **  (IntArray.missing_i_shape out_pre i i n_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_6 := 
forall (out_pre: Z) (n_pre: Z) (years_pre: Z) (input_years: (@list Z)) (prev: Z) (done: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (input_years)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1000 <= (Znth k input_years 0)) /\ ((Znth k input_years 0) <= 9999)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (i = (Zlength (done)))) (PreH9 : (prev = (PreviousYear (done)))) (PreH10 : (GreedyPrefix input_years done )) ,
  ((( &( "years" ) )) # Ptr  |-> years_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "prev" ) )) # Int  |-> prev)
  **  (IntArray.full years_pre n_pre input_years )
  **  (IntArray.seg out_pre 0 i done )
  **  (IntArray.seg_shape out_pre i n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_entail_wit_1 := 
(
forall (out_pre: Z) (n_pre: Z) (years_pre: Z) (input_years: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1000 <= (Znth i input_years 0)) /\ ((Znth i input_years 0) <= 9999)))) (PreH4 : (n_pre = (Zlength (input_years)))) ,
  (IntArray.full years_pre n_pre input_years )
  **  (IntArray.full_shape out_pre n_pre )
|--
  EX (done: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (n_pre = (Zlength (input_years))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1000 <= (Znth k input_years 0)) /\ ((Znth k input_years 0) <= 9999))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 = (Zlength (done))) ” 
  &&  “ (1000 = (PreviousYear (done))) ” 
  &&  “ (GreedyPrefix input_years done ) ”
  &&  (IntArray.full years_pre n_pre input_years )
  **  (IntArray.seg out_pre 0 0 done )
  **  (IntArray.seg_shape out_pre 0 n_pre )
) \/
(
forall (out_pre: Z) (n_pre: Z) (input_years: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1000 <= (Znth i input_years 0)) /\ ((Znth i input_years 0) <= 9999)))) (PreH4 : (n_pre = (Zlength (input_years)))) ,
  (IntArray.full_shape out_pre n_pre )
|--
  “ (GreedyPrefix input_years (@nil Z) ) ” 
  &&  “ (1000 = (PreviousYear ((@nil Z)))) ” 
  &&  “ (0 = (Zlength ((@nil Z)))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1000 <= (Znth k input_years 0)) /\ ((Znth k input_years 0) <= 9999))) ”
  &&  (IntArray.seg_shape out_pre 0 n_pre )
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (out_pre: Z) (n_pre: Z) (input_years: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1000 <= (Znth i input_years 0)) /\ ((Znth i input_years 0) <= 9999)))) (PreH4 : (n_pre = (Zlength (input_years)))) ,
  (IntArray.full_shape out_pre n_pre )
|--
  “ (GreedyPrefix input_years (@nil Z) ) ”
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (out_pre: Z) (n_pre: Z) (input_years: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1000 <= (Znth i input_years 0)) /\ ((Znth i input_years 0) <= 9999)))) (PreH4 : (n_pre = (Zlength (input_years)))) ,
  (IntArray.full_shape out_pre n_pre )
|--
  “ (1000 = (PreviousYear ((@nil Z)))) ”
.

Definition solver_entail_wit_1_split_goal_3 := 
forall (out_pre: Z) (n_pre: Z) (input_years: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1000 <= (Znth i input_years 0)) /\ ((Znth i input_years 0) <= 9999)))) (PreH4 : (n_pre = (Zlength (input_years)))) ,
  (IntArray.full_shape out_pre n_pre )
|--
  “ (0 = (Zlength ((@nil Z)))) ”
.

Definition solver_entail_wit_1_split_goal_4 := 
forall (out_pre: Z) (n_pre: Z) (input_years: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1000 <= (Znth i input_years 0)) /\ ((Znth i input_years 0) <= 9999)))) (PreH4 : (n_pre = (Zlength (input_years)))) ,
  (IntArray.full_shape out_pre n_pre )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1000 <= (Znth k input_years 0)) /\ ((Znth k input_years 0) <= 9999))) ”
.

Definition solver_entail_wit_1_split_goal_spatial := 
forall (out_pre: Z) (n_pre: Z) (input_years: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1000 <= (Znth i input_years 0)) /\ ((Znth i input_years 0) <= 9999)))) (PreH4 : (n_pre = (Zlength (input_years)))) ,
  (IntArray.full_shape out_pre n_pre )
|--
  (IntArray.seg_shape out_pre 0 n_pre )
.

Definition solver_entail_wit_2 := 
(
forall (out_pre: Z) (n_pre: Z) (years_pre: Z) (input_years: (@list Z)) (prev: Z) (done_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (input_years)))) (PreH5 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1000 <= (Znth k_2 input_years 0)) /\ ((Znth k_2 input_years 0) <= 9999)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (i = (Zlength (done_2)))) (PreH9 : (prev = (PreviousYear (done_2)))) (PreH10 : (GreedyPrefix input_years done_2 )) ,
  (IntArray.full years_pre n_pre input_years )
  **  (IntArray.seg out_pre 0 i done_2 )
  **  (IntArray.seg_shape out_pre i n_pre )
|--
  EX (old_out: Z)  (done: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (n_pre = (Zlength (input_years))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1000 <= (Znth k input_years 0)) /\ ((Znth k input_years 0) <= 9999))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (i = (Zlength (done))) ” 
  &&  “ (prev = (PreviousYear (done))) ” 
  &&  “ (GreedyPrefix input_years done ) ”
  &&  (IntArray.full years_pre n_pre input_years )
  **  (IntArray.seg out_pre 0 i done )
  **  (((out_pre + (i * sizeof(INT)))) # Int  |-> old_out)
  **  (IntArray.missing_i_shape out_pre i i n_pre )
) \/
(
forall (out_pre: Z) (n_pre: Z) (input_years: (@list Z)) (prev: Z) (done_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (input_years)))) (PreH5 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1000 <= (Znth k_2 input_years 0)) /\ ((Znth k_2 input_years 0) <= 9999)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (i = (Zlength (done_2)))) (PreH9 : (prev = (PreviousYear (done_2)))) (PreH10 : (GreedyPrefix input_years done_2 )) ,
  (IntArray.seg_shape out_pre (i + 1 ) n_pre )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1000 <= (Znth k input_years 0)) /\ ((Znth k input_years 0) <= 9999))) ”
  &&  (IntArray.missing_i_shape out_pre i i n_pre )
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (out_pre: Z) (n_pre: Z) (input_years: (@list Z)) (prev: Z) (done_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (input_years)))) (PreH5 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1000 <= (Znth k_2 input_years 0)) /\ ((Znth k_2 input_years 0) <= 9999)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (i = (Zlength (done_2)))) (PreH9 : (prev = (PreviousYear (done_2)))) (PreH10 : (GreedyPrefix input_years done_2 )) ,
  (IntArray.seg_shape out_pre (i + 1 ) n_pre )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1000 <= (Znth k input_years 0)) /\ ((Znth k input_years 0) <= 9999))) ”
.

Definition solver_entail_wit_2_split_goal_spatial := 
forall (out_pre: Z) (n_pre: Z) (input_years: (@list Z)) (prev: Z) (done_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (input_years)))) (PreH5 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1000 <= (Znth k_2 input_years 0)) /\ ((Znth k_2 input_years 0) <= 9999)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (i = (Zlength (done_2)))) (PreH9 : (prev = (PreviousYear (done_2)))) (PreH10 : (GreedyPrefix input_years done_2 )) ,
  (IntArray.seg_shape out_pre (i + 1 ) n_pre )
|--
  (IntArray.missing_i_shape out_pre i i n_pre )
.

Definition solver_entail_wit_3 := 
(
forall (out_pre: Z) (n_pre: Z) (years_pre: Z) (input_years: (@list Z)) (done_2: (@list Z)) (old_out: Z) (i: Z) (prev: Z) (retval: Z) (PreH1 : ((Znth i (replace_Znth (i) (retval) ((app (done_2) ((cons (old_out) ((@nil Z))))))) 0) >= 0)) (PreH2 : (NextYearResult (Znth i input_years 0) prev retval )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (n_pre = (Zlength (input_years)))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1000 <= (Znth k_2 input_years 0)) /\ ((Znth k_2 input_years 0) <= 9999)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (i = (Zlength (done_2)))) (PreH10 : (prev = (PreviousYear (done_2)))) (PreH11 : (GreedyPrefix input_years done_2 )) ,
  (IntArray.full out_pre (i + 1 ) (replace_Znth (i) (retval) ((app (done_2) ((cons (old_out) ((@nil Z))))))) )
  **  (IntArray.full years_pre n_pre input_years )
  **  (IntArray.missing_i_shape out_pre i i n_pre )
|--
  EX (done: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (n_pre = (Zlength (input_years))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1000 <= (Znth k input_years 0)) /\ ((Znth k input_years 0) <= 9999))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((i + 1 ) = (Zlength (done))) ” 
  &&  “ ((Znth i (replace_Znth (i) (retval) ((app (done_2) ((cons (old_out) ((@nil Z))))))) 0) = (PreviousYear (done))) ” 
  &&  “ (GreedyPrefix input_years done ) ”
  &&  (IntArray.full years_pre n_pre input_years )
  **  (IntArray.seg out_pre 0 (i + 1 ) done )
  **  (IntArray.seg_shape out_pre (i + 1 ) n_pre )
) \/
(
forall (out_pre: Z) (n_pre: Z) (input_years: (@list Z)) (done_2: (@list Z)) (old_out: Z) (i: Z) (prev: Z) (retval: Z) (PreH1 : ((Znth i (replace_Znth (i) (retval) ((app (done_2) ((cons (old_out) ((@nil Z))))))) 0) >= 0)) (PreH2 : (NextYearResult (Znth i input_years 0) prev retval )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (n_pre = (Zlength (input_years)))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1000 <= (Znth k_2 input_years 0)) /\ ((Znth k_2 input_years 0) <= 9999)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (i = (Zlength (done_2)))) (PreH10 : (prev = (PreviousYear (done_2)))) (PreH11 : (GreedyPrefix input_years done_2 )) ,
  (IntArray.full out_pre (i + 1 ) (replace_Znth (i) (retval) ((app (done_2) ((cons (old_out) ((@nil Z))))))) )
  **  (IntArray.missing_i_shape out_pre i i n_pre )
|--
  EX (done: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (n_pre = (Zlength (input_years))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1000 <= (Znth k input_years 0)) /\ ((Znth k input_years 0) <= 9999))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((i + 1 ) = (Zlength (done))) ” 
  &&  “ ((Znth i (replace_Znth (i) (retval) ((app (done_2) ((cons (old_out) ((@nil Z))))))) 0) = (PreviousYear (done))) ” 
  &&  “ (GreedyPrefix input_years done ) ”
  &&  (IntArray.seg out_pre 0 (i + 1 ) done )
  **  (IntArray.seg_shape out_pre (i + 1 ) n_pre )
).

Definition solver_return_wit_1 := 
(
forall (out_pre: Z) (n_pre: Z) (years_pre: Z) (input_years: (@list Z)) (prev: Z) (done: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (input_years)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1000 <= (Znth k input_years 0)) /\ ((Znth k input_years 0) <= 9999)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (i = (Zlength (done)))) (PreH9 : (prev = (PreviousYear (done)))) (PreH10 : (GreedyPrefix input_years done )) ,
  (IntArray.full years_pre n_pre input_years )
  **  (IntArray.seg out_pre 0 i done )
  **  (IntArray.seg_shape out_pre i n_pre )
|--
  EX (result: (@list Z)) ,
  “ (1 = 1) ” 
  &&  “ (Spec input_years (Some (result)) ) ”
  &&  (IntArray.full out_pre n_pre result )
  **  (IntArray.full years_pre n_pre input_years )
) \/
(
forall (out_pre: Z) (n_pre: Z) (input_years: (@list Z)) (prev: Z) (done: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (input_years)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1000 <= (Znth k input_years 0)) /\ ((Znth k input_years 0) <= 9999)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (i = (Zlength (done)))) (PreH9 : (prev = (PreviousYear (done)))) (PreH10 : (GreedyPrefix input_years done )) ,
  (IntArray.seg out_pre 0 i done )
|--
  EX (result: (@list Z)) ,
  “ (Spec input_years (Some (result)) ) ”
  &&  (IntArray.full out_pre n_pre result )
).

Definition solver_return_wit_2 := 
(
forall (out_pre: Z) (n_pre: Z) (years_pre: Z) (input_years: (@list Z)) (done: (@list Z)) (old_out: Z) (i: Z) (prev: Z) (retval: Z) (PreH1 : ((Znth i (replace_Znth (i) (retval) ((app (done) ((cons (old_out) ((@nil Z))))))) 0) < 0)) (PreH2 : (NextYearResult (Znth i input_years 0) prev retval )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (n_pre = (Zlength (input_years)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1000 <= (Znth k input_years 0)) /\ ((Znth k input_years 0) <= 9999)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (i = (Zlength (done)))) (PreH10 : (prev = (PreviousYear (done)))) (PreH11 : (GreedyPrefix input_years done )) ,
  (IntArray.full out_pre (i + 1 ) (replace_Znth (i) (retval) ((app (done) ((cons (old_out) ((@nil Z))))))) )
  **  (IntArray.full years_pre n_pre input_years )
  **  (IntArray.missing_i_shape out_pre i i n_pre )
|--
  “ (0 = 0) ” 
  &&  “ (Spec input_years None ) ”
  &&  (IntArray.full_shape out_pre n_pre )
  **  (IntArray.full years_pre n_pre input_years )
) \/
(
forall (out_pre: Z) (n_pre: Z) (input_years: (@list Z)) (done: (@list Z)) (old_out: Z) (i: Z) (prev: Z) (retval: Z) (PreH1 : ((Znth i (replace_Znth (i) (retval) ((app (done) ((cons (old_out) ((@nil Z))))))) 0) < 0)) (PreH2 : (NextYearResult (Znth i input_years 0) prev retval )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (n_pre = (Zlength (input_years)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1000 <= (Znth k input_years 0)) /\ ((Znth k input_years 0) <= 9999)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (i = (Zlength (done)))) (PreH10 : (prev = (PreviousYear (done)))) (PreH11 : (GreedyPrefix input_years done )) ,
  (IntArray.full out_pre (i + 1 ) (replace_Znth (i) (retval) ((app (done) ((cons (old_out) ((@nil Z))))))) )
  **  (IntArray.missing_i_shape out_pre i i n_pre )
|--
  “ (Spec input_years None ) ”
  &&  (IntArray.full_shape out_pre n_pre )
).

Definition solver_return_wit_2_split_goal_1 := 
forall (out_pre: Z) (n_pre: Z) (input_years: (@list Z)) (done: (@list Z)) (old_out: Z) (i: Z) (prev: Z) (retval: Z) (PreH1 : ((Znth i (replace_Znth (i) (retval) ((app (done) ((cons (old_out) ((@nil Z))))))) 0) < 0)) (PreH2 : (NextYearResult (Znth i input_years 0) prev retval )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (n_pre = (Zlength (input_years)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1000 <= (Znth k input_years 0)) /\ ((Znth k input_years 0) <= 9999)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (i = (Zlength (done)))) (PreH10 : (prev = (PreviousYear (done)))) (PreH11 : (GreedyPrefix input_years done )) ,
  (IntArray.full out_pre (i + 1 ) (replace_Znth (i) (retval) ((app (done) ((cons (old_out) ((@nil Z))))))) )
  **  (IntArray.missing_i_shape out_pre i i n_pre )
|--
  “ (Spec input_years None ) ”
.

Definition solver_return_wit_2_split_goal_spatial := 
forall (out_pre: Z) (n_pre: Z) (input_years: (@list Z)) (done: (@list Z)) (old_out: Z) (i: Z) (prev: Z) (retval: Z) (PreH1 : ((Znth i (replace_Znth (i) (retval) ((app (done) ((cons (old_out) ((@nil Z))))))) 0) < 0)) (PreH2 : (NextYearResult (Znth i input_years 0) prev retval )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (n_pre = (Zlength (input_years)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1000 <= (Znth k input_years 0)) /\ ((Znth k input_years 0) <= 9999)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (i = (Zlength (done)))) (PreH10 : (prev = (PreviousYear (done)))) (PreH11 : (GreedyPrefix input_years done )) ,
  (IntArray.full out_pre (i + 1 ) (replace_Znth (i) (retval) ((app (done) ((cons (old_out) ((@nil Z))))))) )
  **  (IntArray.missing_i_shape out_pre i i n_pre )
|--
  (IntArray.full_shape out_pre n_pre )
.

Definition solver_partial_solve_wit_1 := 
forall (out_pre: Z) (n_pre: Z) (years_pre: Z) (input_years: (@list Z)) (done: (@list Z)) (old_out: Z) (i: Z) (prev: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (n_pre = (Zlength (input_years)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1000 <= (Znth k input_years 0)) /\ ((Znth k input_years 0) <= 9999)))) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (i = (Zlength (done)))) (PreH8 : (prev = (PreviousYear (done)))) (PreH9 : (GreedyPrefix input_years done )) ,
  (IntArray.full years_pre n_pre input_years )
  **  (IntArray.seg out_pre 0 i done )
  **  (((out_pre + (i * sizeof(INT)))) # Int  |-> old_out)
  **  (IntArray.missing_i_shape out_pre i i n_pre )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (n_pre = (Zlength (input_years))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1000 <= (Znth k input_years 0)) /\ ((Znth k input_years 0) <= 9999))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (i = (Zlength (done))) ” 
  &&  “ (prev = (PreviousYear (done))) ” 
  &&  “ (GreedyPrefix input_years done ) ”
  &&  (((years_pre + (i * sizeof(INT)))) # Int  |-> (Znth i input_years 0))
  **  (IntArray.missing_i years_pre i 0 n_pre input_years )
  **  (IntArray.seg out_pre 0 i done )
  **  (((out_pre + (i * sizeof(INT)))) # Int  |-> old_out)
  **  (IntArray.missing_i_shape out_pre i i n_pre )
.

Definition solver_partial_solve_wit_2_pure := 
(
forall (out_pre: Z) (n_pre: Z) (years_pre: Z) (input_years: (@list Z)) (done: (@list Z)) (old_out: Z) (i: Z) (prev: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (n_pre = (Zlength (input_years)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1000 <= (Znth k input_years 0)) /\ ((Znth k input_years 0) <= 9999)))) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (i = (Zlength (done)))) (PreH8 : (prev = (PreviousYear (done)))) (PreH9 : (GreedyPrefix input_years done )) ,
  (IntArray.seg out_pre 0 (i + 1 ) (app (done) ((cons (old_out) ((@nil Z))))) )
  **  (IntArray.full years_pre n_pre input_years )
  **  ((( &( "years" ) )) # Ptr  |-> years_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "prev" ) )) # Int  |-> prev)
  **  (IntArray.missing_i_shape out_pre i i n_pre )
|--
  “ (1000 <= (Znth i input_years 0)) ” 
  &&  “ ((Znth i input_years 0) <= 9999) ” 
  &&  “ (prev <= 2011) ” 
  &&  “ (1000 <= prev) ”
) \/
(
forall (out_pre: Z) (n_pre: Z) (years_pre: Z) (input_years: (@list Z)) (done: (@list Z)) (old_out: Z) (i: Z) (prev: Z) (PreH1 : (prev <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (prev >= INT_MIN)) (PreH5 : (i >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (n_pre = (Zlength (input_years)))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1000 <= (Znth k input_years 0)) /\ ((Znth k input_years 0) <= 9999)))) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (i = (Zlength (done)))) (PreH14 : (prev = (PreviousYear (done)))) (PreH15 : (GreedyPrefix input_years done )) ,
  (IntArray.seg out_pre 0 (i + 1 ) (app (done) ((cons (old_out) ((@nil Z))))) )
  **  (IntArray.full years_pre n_pre input_years )
  **  ((( &( "years" ) )) # Ptr  |-> years_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "prev" ) )) # Int  |-> prev)
  **  (IntArray.missing_i_shape out_pre i i n_pre )
|--
  “ (1000 <= prev) ” 
  &&  “ (prev <= 2011) ”
).

Definition solver_partial_solve_wit_2_pure_split_goal_1 := 
forall (out_pre: Z) (n_pre: Z) (years_pre: Z) (input_years: (@list Z)) (done: (@list Z)) (old_out: Z) (i: Z) (prev: Z) (PreH1 : (prev <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (prev >= INT_MIN)) (PreH5 : (i >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (n_pre = (Zlength (input_years)))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1000 <= (Znth k input_years 0)) /\ ((Znth k input_years 0) <= 9999)))) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (i = (Zlength (done)))) (PreH14 : (prev = (PreviousYear (done)))) (PreH15 : (GreedyPrefix input_years done )) ,
  (IntArray.seg out_pre 0 (i + 1 ) (app (done) ((cons (old_out) ((@nil Z))))) )
  **  (IntArray.full years_pre n_pre input_years )
  **  ((( &( "years" ) )) # Ptr  |-> years_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "prev" ) )) # Int  |-> prev)
  **  (IntArray.missing_i_shape out_pre i i n_pre )
|--
  “ (1000 <= prev) ”
.

Definition solver_partial_solve_wit_2_pure_split_goal_2 := 
forall (out_pre: Z) (n_pre: Z) (years_pre: Z) (input_years: (@list Z)) (done: (@list Z)) (old_out: Z) (i: Z) (prev: Z) (PreH1 : (prev <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (prev >= INT_MIN)) (PreH5 : (i >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (n_pre = (Zlength (input_years)))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1000 <= (Znth k input_years 0)) /\ ((Znth k input_years 0) <= 9999)))) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (i = (Zlength (done)))) (PreH14 : (prev = (PreviousYear (done)))) (PreH15 : (GreedyPrefix input_years done )) ,
  (IntArray.seg out_pre 0 (i + 1 ) (app (done) ((cons (old_out) ((@nil Z))))) )
  **  (IntArray.full years_pre n_pre input_years )
  **  ((( &( "years" ) )) # Ptr  |-> years_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "prev" ) )) # Int  |-> prev)
  **  (IntArray.missing_i_shape out_pre i i n_pre )
|--
  “ (prev <= 2011) ”
.

Definition solver_partial_solve_wit_2_aux := 
forall (out_pre: Z) (n_pre: Z) (years_pre: Z) (input_years: (@list Z)) (done: (@list Z)) (old_out: Z) (i: Z) (prev: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (n_pre = (Zlength (input_years)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1000 <= (Znth k input_years 0)) /\ ((Znth k input_years 0) <= 9999)))) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (i = (Zlength (done)))) (PreH8 : (prev = (PreviousYear (done)))) (PreH9 : (GreedyPrefix input_years done )) ,
  (IntArray.seg out_pre 0 (i + 1 ) (app (done) ((cons (old_out) ((@nil Z))))) )
  **  (IntArray.full years_pre n_pre input_years )
  **  (IntArray.missing_i_shape out_pre i i n_pre )
|--
  “ (1000 <= (Znth i input_years 0)) ” 
  &&  “ ((Znth i input_years 0) <= 9999) ” 
  &&  “ (prev <= 2011) ” 
  &&  “ (1000 <= prev) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (n_pre = (Zlength (input_years))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1000 <= (Znth k input_years 0)) /\ ((Znth k input_years 0) <= 9999))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (i = (Zlength (done))) ” 
  &&  “ (prev = (PreviousYear (done))) ” 
  &&  “ (GreedyPrefix input_years done ) ”
  &&  (IntArray.seg out_pre 0 (i + 1 ) (app (done) ((cons (old_out) ((@nil Z))))) )
  **  (IntArray.full years_pre n_pre input_years )
  **  (IntArray.missing_i_shape out_pre i i n_pre )
.

Definition solver_partial_solve_wit_2 := solver_partial_solve_wit_2_pure -> solver_partial_solve_wit_2_aux.

Definition solver_partial_solve_wit_3 := 
forall (out_pre: Z) (n_pre: Z) (years_pre: Z) (input_years: (@list Z)) (done: (@list Z)) (old_out: Z) (i: Z) (prev: Z) (retval: Z) (PreH1 : (NextYearResult (Znth i input_years 0) prev retval )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (input_years)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1000 <= (Znth k input_years 0)) /\ ((Znth k input_years 0) <= 9999)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (i = (Zlength (done)))) (PreH9 : (prev = (PreviousYear (done)))) (PreH10 : (GreedyPrefix input_years done )) ,
  (IntArray.seg out_pre 0 (i + 1 ) (app (done) ((cons (old_out) ((@nil Z))))) )
  **  (IntArray.full years_pre n_pre input_years )
  **  (IntArray.missing_i_shape out_pre i i n_pre )
|--
  “ (NextYearResult (Znth i input_years 0) prev retval ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (n_pre = (Zlength (input_years))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1000 <= (Znth k input_years 0)) /\ ((Znth k input_years 0) <= 9999))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (i = (Zlength (done))) ” 
  &&  “ (prev = (PreviousYear (done))) ” 
  &&  “ (GreedyPrefix input_years done ) ”
  &&  (((out_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i out_pre i 0 (i + 1 ) (app (done) ((cons (old_out) ((@nil Z))))) )
  **  (IntArray.full years_pre n_pre input_years )
  **  (IntArray.missing_i_shape out_pre i i n_pre )
.

Definition solver_partial_solve_wit_4 := 
forall (out_pre: Z) (n_pre: Z) (years_pre: Z) (input_years: (@list Z)) (done: (@list Z)) (old_out: Z) (i: Z) (prev: Z) (retval: Z) (PreH1 : (NextYearResult (Znth i input_years 0) prev retval )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (n_pre = (Zlength (input_years)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1000 <= (Znth k input_years 0)) /\ ((Znth k input_years 0) <= 9999)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (i = (Zlength (done)))) (PreH9 : (prev = (PreviousYear (done)))) (PreH10 : (GreedyPrefix input_years done )) ,
  (IntArray.full out_pre (i + 1 ) (replace_Znth (i) (retval) ((app (done) ((cons (old_out) ((@nil Z))))))) )
  **  (IntArray.full years_pre n_pre input_years )
  **  (IntArray.missing_i_shape out_pre i i n_pre )
|--
  “ (NextYearResult (Znth i input_years 0) prev retval ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (n_pre = (Zlength (input_years))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1000 <= (Znth k input_years 0)) /\ ((Znth k input_years 0) <= 9999))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (i = (Zlength (done))) ” 
  &&  “ (prev = (PreviousYear (done))) ” 
  &&  “ (GreedyPrefix input_years done ) ”
  &&  (((out_pre + (i * sizeof(INT)))) # Int  |-> (Znth i (replace_Znth (i) (retval) ((app (done) ((cons (old_out) ((@nil Z))))))) 0))
  **  (IntArray.missing_i out_pre i 0 (i + 1 ) (replace_Znth (i) (retval) ((app (done) ((cons (old_out) ((@nil Z))))))) )
  **  (IntArray.full years_pre n_pre input_years )
  **  (IntArray.missing_i_shape out_pre i i n_pre )
.

Definition solver_partial_solve_wit_5 := 
forall (out_pre: Z) (n_pre: Z) (years_pre: Z) (input_years: (@list Z)) (done: (@list Z)) (old_out: Z) (i: Z) (prev: Z) (retval: Z) (PreH1 : ((Znth i (replace_Znth (i) (retval) ((app (done) ((cons (old_out) ((@nil Z))))))) 0) >= 0)) (PreH2 : (NextYearResult (Znth i input_years 0) prev retval )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (n_pre = (Zlength (input_years)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1000 <= (Znth k input_years 0)) /\ ((Znth k input_years 0) <= 9999)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (i = (Zlength (done)))) (PreH10 : (prev = (PreviousYear (done)))) (PreH11 : (GreedyPrefix input_years done )) ,
  (IntArray.full out_pre (i + 1 ) (replace_Znth (i) (retval) ((app (done) ((cons (old_out) ((@nil Z))))))) )
  **  (IntArray.full years_pre n_pre input_years )
  **  (IntArray.missing_i_shape out_pre i i n_pre )
|--
  “ ((Znth i (replace_Znth (i) (retval) ((app (done) ((cons (old_out) ((@nil Z))))))) 0) >= 0) ” 
  &&  “ (NextYearResult (Znth i input_years 0) prev retval ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (n_pre = (Zlength (input_years))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1000 <= (Znth k input_years 0)) /\ ((Znth k input_years 0) <= 9999))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (i = (Zlength (done))) ” 
  &&  “ (prev = (PreviousYear (done))) ” 
  &&  “ (GreedyPrefix input_years done ) ”
  &&  (((out_pre + (i * sizeof(INT)))) # Int  |-> (Znth i (replace_Znth (i) (retval) ((app (done) ((cons (old_out) ((@nil Z))))))) 0))
  **  (IntArray.missing_i out_pre i 0 (i + 1 ) (replace_Znth (i) (retval) ((app (done) ((cons (old_out) ((@nil Z))))))) )
  **  (IntArray.full years_pre n_pre input_years )
  **  (IntArray.missing_i_shape out_pre i i n_pre )
.

Module Type VC_Correct.


Axiom proof_of_next_year_safety_wit_1 : next_year_safety_wit_1.
Axiom proof_of_next_year_safety_wit_2 : next_year_safety_wit_2.
Axiom proof_of_next_year_safety_wit_3 : next_year_safety_wit_3.
Axiom proof_of_next_year_safety_wit_4 : next_year_safety_wit_4.
Axiom proof_of_next_year_safety_wit_5 : next_year_safety_wit_5.
Axiom proof_of_next_year_safety_wit_6 : next_year_safety_wit_6.
Axiom proof_of_next_year_safety_wit_7 : next_year_safety_wit_7.
Axiom proof_of_next_year_safety_wit_8 : next_year_safety_wit_8.
Axiom proof_of_next_year_safety_wit_9 : next_year_safety_wit_9.
Axiom proof_of_next_year_safety_wit_10 : next_year_safety_wit_10.
Axiom proof_of_next_year_safety_wit_11 : next_year_safety_wit_11.
Axiom proof_of_next_year_safety_wit_12 : next_year_safety_wit_12.
Axiom proof_of_next_year_safety_wit_13 : next_year_safety_wit_13.
Axiom proof_of_next_year_safety_wit_14 : next_year_safety_wit_14.
Axiom proof_of_next_year_safety_wit_15 : next_year_safety_wit_15.
Axiom proof_of_next_year_safety_wit_16 : next_year_safety_wit_16.
Axiom proof_of_next_year_safety_wit_17 : next_year_safety_wit_17.
Axiom proof_of_next_year_safety_wit_18 : next_year_safety_wit_18.
Axiom proof_of_next_year_safety_wit_19 : next_year_safety_wit_19.
Axiom proof_of_next_year_safety_wit_20 : next_year_safety_wit_20.
Axiom proof_of_next_year_safety_wit_21 : next_year_safety_wit_21.
Axiom proof_of_next_year_safety_wit_22 : next_year_safety_wit_22.
Axiom proof_of_next_year_safety_wit_23 : next_year_safety_wit_23.
Axiom proof_of_next_year_safety_wit_24 : next_year_safety_wit_24.
Axiom proof_of_next_year_safety_wit_25 : next_year_safety_wit_25.
Axiom proof_of_next_year_safety_wit_26 : next_year_safety_wit_26.
Axiom proof_of_next_year_safety_wit_27 : next_year_safety_wit_27.
Axiom proof_of_next_year_safety_wit_28 : next_year_safety_wit_28.
Axiom proof_of_next_year_safety_wit_29 : next_year_safety_wit_29.
Axiom proof_of_next_year_safety_wit_30 : next_year_safety_wit_30.
Axiom proof_of_next_year_safety_wit_31 : next_year_safety_wit_31.
Axiom proof_of_next_year_safety_wit_32 : next_year_safety_wit_32.
Axiom proof_of_next_year_safety_wit_33 : next_year_safety_wit_33.
Axiom proof_of_next_year_safety_wit_34 : next_year_safety_wit_34.
Axiom proof_of_next_year_safety_wit_35 : next_year_safety_wit_35.
Axiom proof_of_next_year_safety_wit_36 : next_year_safety_wit_36.
Axiom proof_of_next_year_safety_wit_37 : next_year_safety_wit_37.
Axiom proof_of_next_year_safety_wit_38 : next_year_safety_wit_38.
Axiom proof_of_next_year_safety_wit_39 : next_year_safety_wit_39.
Axiom proof_of_next_year_safety_wit_40 : next_year_safety_wit_40.
Axiom proof_of_next_year_safety_wit_41 : next_year_safety_wit_41.
Axiom proof_of_next_year_safety_wit_42 : next_year_safety_wit_42.
Axiom proof_of_next_year_safety_wit_43 : next_year_safety_wit_43.
Axiom proof_of_next_year_safety_wit_44 : next_year_safety_wit_44.
Axiom proof_of_next_year_safety_wit_45 : next_year_safety_wit_45.
Axiom proof_of_next_year_safety_wit_46 : next_year_safety_wit_46.
Axiom proof_of_next_year_safety_wit_47 : next_year_safety_wit_47.
Axiom proof_of_next_year_safety_wit_48 : next_year_safety_wit_48.
Axiom proof_of_next_year_safety_wit_49 : next_year_safety_wit_49.
Axiom proof_of_next_year_safety_wit_50 : next_year_safety_wit_50.
Axiom proof_of_next_year_safety_wit_51 : next_year_safety_wit_51.
Axiom proof_of_next_year_safety_wit_52 : next_year_safety_wit_52.
Axiom proof_of_next_year_safety_wit_53 : next_year_safety_wit_53.
Axiom proof_of_next_year_safety_wit_54 : next_year_safety_wit_54.
Axiom proof_of_next_year_safety_wit_55 : next_year_safety_wit_55.
Axiom proof_of_next_year_safety_wit_56 : next_year_safety_wit_56.
Axiom proof_of_next_year_safety_wit_57 : next_year_safety_wit_57.
Axiom proof_of_next_year_safety_wit_58 : next_year_safety_wit_58.
Axiom proof_of_next_year_safety_wit_59 : next_year_safety_wit_59.
Axiom proof_of_next_year_safety_wit_60 : next_year_safety_wit_60.
Axiom proof_of_next_year_safety_wit_61 : next_year_safety_wit_61.
Axiom proof_of_next_year_safety_wit_62 : next_year_safety_wit_62.
Axiom proof_of_next_year_safety_wit_63 : next_year_safety_wit_63.
Axiom proof_of_next_year_safety_wit_64 : next_year_safety_wit_64.
Axiom proof_of_next_year_safety_wit_65 : next_year_safety_wit_65.
Axiom proof_of_next_year_safety_wit_66 : next_year_safety_wit_66.
Axiom proof_of_next_year_safety_wit_67 : next_year_safety_wit_67.
Axiom proof_of_next_year_entail_wit_1 : next_year_entail_wit_1.
Axiom proof_of_next_year_entail_wit_2_1 : next_year_entail_wit_2_1.
Axiom proof_of_next_year_entail_wit_2_2 : next_year_entail_wit_2_2.
Axiom proof_of_next_year_entail_wit_3_1 : next_year_entail_wit_3_1.
Axiom proof_of_next_year_entail_wit_3_2 : next_year_entail_wit_3_2.
Axiom proof_of_next_year_entail_wit_3_3 : next_year_entail_wit_3_3.
Axiom proof_of_next_year_entail_wit_3_4 : next_year_entail_wit_3_4.
Axiom proof_of_next_year_entail_wit_3_5 : next_year_entail_wit_3_5.
Axiom proof_of_next_year_entail_wit_3_6 : next_year_entail_wit_3_6.
Axiom proof_of_next_year_entail_wit_3_7 : next_year_entail_wit_3_7.
Axiom proof_of_next_year_entail_wit_3_8 : next_year_entail_wit_3_8.
Axiom proof_of_next_year_entail_wit_3_9 : next_year_entail_wit_3_9.
Axiom proof_of_next_year_entail_wit_3_10 : next_year_entail_wit_3_10.
Axiom proof_of_next_year_entail_wit_3_11 : next_year_entail_wit_3_11.
Axiom proof_of_next_year_entail_wit_3_12 : next_year_entail_wit_3_12.
Axiom proof_of_next_year_entail_wit_4_1 : next_year_entail_wit_4_1.
Axiom proof_of_next_year_entail_wit_4_2 : next_year_entail_wit_4_2.
Axiom proof_of_next_year_return_wit_1 : next_year_return_wit_1.
Axiom proof_of_next_year_partial_solve_wit_1 : next_year_partial_solve_wit_1.
Axiom proof_of_next_year_partial_solve_wit_2 : next_year_partial_solve_wit_2.
Axiom proof_of_next_year_partial_solve_wit_3 : next_year_partial_solve_wit_3.
Axiom proof_of_next_year_partial_solve_wit_4 : next_year_partial_solve_wit_4.
Axiom proof_of_next_year_partial_solve_wit_5 : next_year_partial_solve_wit_5.
Axiom proof_of_next_year_partial_solve_wit_6 : next_year_partial_solve_wit_6.
Axiom proof_of_next_year_partial_solve_wit_7 : next_year_partial_solve_wit_7.
Axiom proof_of_next_year_partial_solve_wit_8 : next_year_partial_solve_wit_8.
Axiom proof_of_next_year_partial_solve_wit_9 : next_year_partial_solve_wit_9.
Axiom proof_of_next_year_partial_solve_wit_10 : next_year_partial_solve_wit_10.
Axiom proof_of_next_year_partial_solve_wit_11 : next_year_partial_solve_wit_11.
Axiom proof_of_next_year_partial_solve_wit_12 : next_year_partial_solve_wit_12.
Axiom proof_of_next_year_partial_solve_wit_13 : next_year_partial_solve_wit_13.
Axiom proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Axiom proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Axiom proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Axiom proof_of_solver_safety_wit_4 : solver_safety_wit_4.
Axiom proof_of_solver_safety_wit_5 : solver_safety_wit_5.
Axiom proof_of_solver_safety_wit_6 : solver_safety_wit_6.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.

End VC_Correct.
