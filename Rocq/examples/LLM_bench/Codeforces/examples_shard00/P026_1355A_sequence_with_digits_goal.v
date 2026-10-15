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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P026_1355A_sequence_with_digits_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P026_1355A_sequence_with_digits_lib.
Local Open Scope sac.

(*----- Function step -----*)

Definition step_safety_wit_1 := 
forall (x_pre: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1810000000000000000)) ,
  ((( &( "mx" ) )) # Int  |->_)
  **  ((( &( "mn" ) )) # Int  |-> 9)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition step_safety_wit_2 := 
forall (x_pre: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1810000000000000000)) ,
  ((( &( "mn" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
|--
  “ (9 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 9) ”
.

Definition step_safety_wit_3 := 
forall (x_pre: Z) (mx: Z) (mn: Z) (x: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1810000000000000000)) (PreH3 : (0 <= x)) (PreH4 : (x <= x_pre)) (PreH5 : (0 <= mn)) (PreH6 : (mn <= 9)) (PreH7 : (0 <= mx)) (PreH8 : (mx <= 9)) (PreH9 : (DigitScanState x_pre x mn mx )) (PreH10 : (x <> 0)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "mx" ) )) # Int  |-> mx)
|--
  “ ((x <> (INT64_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition step_safety_wit_4 := 
forall (x_pre: Z) (mx: Z) (mn: Z) (x: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1810000000000000000)) (PreH3 : (0 <= x)) (PreH4 : (x <= x_pre)) (PreH5 : (0 <= mn)) (PreH6 : (mn <= 9)) (PreH7 : (0 <= mx)) (PreH8 : (mx <= 9)) (PreH9 : (DigitScanState x_pre x mn mx )) (PreH10 : (x <> 0)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "mx" ) )) # Int  |-> mx)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition step_safety_wit_5 := 
forall (x_pre: Z) (mx: Z) (mn: Z) (x: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1810000000000000000)) (PreH3 : (0 <= x)) (PreH4 : (x <= x_pre)) (PreH5 : (0 <= mn)) (PreH6 : (mn <= 9)) (PreH7 : (0 <= mx)) (PreH8 : (mx <= 9)) (PreH9 : (DigitScanState x_pre x mn mx )) (PreH10 : (x <> 0)) ,
  ((( &( "d" ) )) # Int  |-> (signed_last_nbits ((x % ( 10 ) )) (32)))
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "mx" ) )) # Int  |-> mx)
|--
  “ ((x <> (INT64_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition step_safety_wit_6 := 
forall (x_pre: Z) (mx: Z) (mn: Z) (x: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1810000000000000000)) (PreH3 : (0 <= x)) (PreH4 : (x <= x_pre)) (PreH5 : (0 <= mn)) (PreH6 : (mn <= 9)) (PreH7 : (0 <= mx)) (PreH8 : (mx <= 9)) (PreH9 : (DigitScanState x_pre x mn mx )) (PreH10 : (x <> 0)) ,
  ((( &( "d" ) )) # Int  |-> (signed_last_nbits ((x % ( 10 ) )) (32)))
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "mx" ) )) # Int  |-> mx)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition step_safety_wit_7 := 
forall (x_pre: Z) (mx: Z) (mn: Z) (x: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1810000000000000000)) (PreH3 : (0 <= x)) (PreH4 : (x <= x_pre)) (PreH5 : (0 <= mn)) (PreH6 : (mn <= 9)) (PreH7 : (0 <= mx)) (PreH8 : (mx <= 9)) (PreH9 : (DigitScanState x_pre x mn mx )) (PreH10 : (x = 0)) ,
  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "mn" ) )) # Int  |-> mn)
  **  ((( &( "mx" ) )) # Int  |-> mx)
|--
  “ ((mn * mx ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (mn * mx )) ”
.

Definition step_entail_wit_1 := 
(
forall (x_pre: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1810000000000000000)) ,
  TT && emp 
|--
  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= 1810000000000000000) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= x_pre) ” 
  &&  “ (0 <= 9) ” 
  &&  “ (9 <= 9) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 9) ” 
  &&  “ (DigitScanState x_pre x_pre 9 0 ) ”
  &&  emp
) \/
(
forall (x_pre: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1810000000000000000)) ,
  TT && emp 
|--
  “ (DigitScanState x_pre x_pre 9 0 ) ”
  &&  emp
).

Definition step_entail_wit_1_split_goal_1 := 
forall (x_pre: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1810000000000000000)) ,
  (DigitScanState x_pre x_pre 9 0 )
.

Definition step_entail_wit_2_1 := 
(
forall (x_pre: Z) (mx: Z) (mn: Z) (x: Z) (PreH1 : ((signed_last_nbits ((x % ( 10 ) )) (32)) > mx)) (PreH2 : ((signed_last_nbits ((x % ( 10 ) )) (32)) < mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : (0 <= x)) (PreH6 : (x <= x_pre)) (PreH7 : (0 <= mn)) (PreH8 : (mn <= 9)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx )) (PreH12 : (x <> 0)) ,
  TT && emp 
|--
  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= 1810000000000000000) ” 
  &&  “ (0 <= (x ÷ 10 )) ” 
  &&  “ ((x ÷ 10 ) <= x_pre) ” 
  &&  “ (0 <= (signed_last_nbits ((x % ( 10 ) )) (32))) ” 
  &&  “ ((signed_last_nbits ((x % ( 10 ) )) (32)) <= 9) ” 
  &&  “ (0 <= (signed_last_nbits ((x % ( 10 ) )) (32))) ” 
  &&  “ ((signed_last_nbits ((x % ( 10 ) )) (32)) <= 9) ” 
  &&  “ (DigitScanState x_pre (x ÷ 10 ) (signed_last_nbits ((x % ( 10 ) )) (32)) (signed_last_nbits ((x % ( 10 ) )) (32)) ) ”
  &&  emp
) \/
(
forall (x_pre: Z) (mx: Z) (mn: Z) (x: Z) (PreH1 : ((signed_last_nbits ((x % ( 10 ) )) (32)) > mx)) (PreH2 : ((signed_last_nbits ((x % ( 10 ) )) (32)) < mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : (0 <= x)) (PreH6 : (x <= x_pre)) (PreH7 : (0 <= mn)) (PreH8 : (mn <= 9)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx )) (PreH12 : (x <> 0)) ,
  TT && emp 
|--
  “ (DigitScanState x_pre (x ÷ 10 ) (signed_last_nbits ((x % ( 10 ) )) (32)) (signed_last_nbits ((x % ( 10 ) )) (32)) ) ” 
  &&  “ ((x ÷ 10 ) <= x_pre) ” 
  &&  “ (0 <= (x ÷ 10 )) ”
  &&  emp
).

Definition step_entail_wit_2_1_split_goal_1 := 
forall (x_pre: Z) (mx: Z) (mn: Z) (x: Z) (PreH1 : ((signed_last_nbits ((x % ( 10 ) )) (32)) > mx)) (PreH2 : ((signed_last_nbits ((x % ( 10 ) )) (32)) < mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : (0 <= x)) (PreH6 : (x <= x_pre)) (PreH7 : (0 <= mn)) (PreH8 : (mn <= 9)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx )) (PreH12 : (x <> 0)) ,
  (DigitScanState x_pre (x ÷ 10 ) (signed_last_nbits ((x % ( 10 ) )) (32)) (signed_last_nbits ((x % ( 10 ) )) (32)) )
.

Definition step_entail_wit_2_1_split_goal_2 := 
forall (x_pre: Z) (mx: Z) (mn: Z) (x: Z) (PreH1 : ((signed_last_nbits ((x % ( 10 ) )) (32)) > mx)) (PreH2 : ((signed_last_nbits ((x % ( 10 ) )) (32)) < mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : (0 <= x)) (PreH6 : (x <= x_pre)) (PreH7 : (0 <= mn)) (PreH8 : (mn <= 9)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx )) (PreH12 : (x <> 0)) ,
  ((x ÷ 10 ) <= x_pre)
.

Definition step_entail_wit_2_1_split_goal_3 := 
forall (x_pre: Z) (mx: Z) (mn: Z) (x: Z) (PreH1 : ((signed_last_nbits ((x % ( 10 ) )) (32)) > mx)) (PreH2 : ((signed_last_nbits ((x % ( 10 ) )) (32)) < mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : (0 <= x)) (PreH6 : (x <= x_pre)) (PreH7 : (0 <= mn)) (PreH8 : (mn <= 9)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx )) (PreH12 : (x <> 0)) ,
  (0 <= (x ÷ 10 ))
.

Definition step_entail_wit_2_2 := 
(
forall (x_pre: Z) (mx: Z) (mn: Z) (x: Z) (PreH1 : ((signed_last_nbits ((x % ( 10 ) )) (32)) > mx)) (PreH2 : ((signed_last_nbits ((x % ( 10 ) )) (32)) >= mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : (0 <= x)) (PreH6 : (x <= x_pre)) (PreH7 : (0 <= mn)) (PreH8 : (mn <= 9)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx )) (PreH12 : (x <> 0)) ,
  TT && emp 
|--
  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= 1810000000000000000) ” 
  &&  “ (0 <= (x ÷ 10 )) ” 
  &&  “ ((x ÷ 10 ) <= x_pre) ” 
  &&  “ (0 <= mn) ” 
  &&  “ (mn <= 9) ” 
  &&  “ (0 <= (signed_last_nbits ((x % ( 10 ) )) (32))) ” 
  &&  “ ((signed_last_nbits ((x % ( 10 ) )) (32)) <= 9) ” 
  &&  “ (DigitScanState x_pre (x ÷ 10 ) mn (signed_last_nbits ((x % ( 10 ) )) (32)) ) ”
  &&  emp
) \/
(
forall (x_pre: Z) (mx: Z) (mn: Z) (x: Z) (PreH1 : ((signed_last_nbits ((x % ( 10 ) )) (32)) > mx)) (PreH2 : ((signed_last_nbits ((x % ( 10 ) )) (32)) >= mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : (0 <= x)) (PreH6 : (x <= x_pre)) (PreH7 : (0 <= mn)) (PreH8 : (mn <= 9)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx )) (PreH12 : (x <> 0)) ,
  TT && emp 
|--
  “ (DigitScanState x_pre (x ÷ 10 ) mn (signed_last_nbits ((x % ( 10 ) )) (32)) ) ” 
  &&  “ ((signed_last_nbits ((x % ( 10 ) )) (32)) <= 9) ” 
  &&  “ ((x ÷ 10 ) <= x_pre) ” 
  &&  “ (0 <= (x ÷ 10 )) ”
  &&  emp
).

Definition step_entail_wit_2_2_split_goal_1 := 
forall (x_pre: Z) (mx: Z) (mn: Z) (x: Z) (PreH1 : ((signed_last_nbits ((x % ( 10 ) )) (32)) > mx)) (PreH2 : ((signed_last_nbits ((x % ( 10 ) )) (32)) >= mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : (0 <= x)) (PreH6 : (x <= x_pre)) (PreH7 : (0 <= mn)) (PreH8 : (mn <= 9)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx )) (PreH12 : (x <> 0)) ,
  (DigitScanState x_pre (x ÷ 10 ) mn (signed_last_nbits ((x % ( 10 ) )) (32)) )
.

Definition step_entail_wit_2_2_split_goal_2 := 
forall (x_pre: Z) (mx: Z) (mn: Z) (x: Z) (PreH1 : ((signed_last_nbits ((x % ( 10 ) )) (32)) > mx)) (PreH2 : ((signed_last_nbits ((x % ( 10 ) )) (32)) >= mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : (0 <= x)) (PreH6 : (x <= x_pre)) (PreH7 : (0 <= mn)) (PreH8 : (mn <= 9)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx )) (PreH12 : (x <> 0)) ,
  ((signed_last_nbits ((x % ( 10 ) )) (32)) <= 9)
.

Definition step_entail_wit_2_2_split_goal_3 := 
forall (x_pre: Z) (mx: Z) (mn: Z) (x: Z) (PreH1 : ((signed_last_nbits ((x % ( 10 ) )) (32)) > mx)) (PreH2 : ((signed_last_nbits ((x % ( 10 ) )) (32)) >= mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : (0 <= x)) (PreH6 : (x <= x_pre)) (PreH7 : (0 <= mn)) (PreH8 : (mn <= 9)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx )) (PreH12 : (x <> 0)) ,
  ((x ÷ 10 ) <= x_pre)
.

Definition step_entail_wit_2_2_split_goal_4 := 
forall (x_pre: Z) (mx: Z) (mn: Z) (x: Z) (PreH1 : ((signed_last_nbits ((x % ( 10 ) )) (32)) > mx)) (PreH2 : ((signed_last_nbits ((x % ( 10 ) )) (32)) >= mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : (0 <= x)) (PreH6 : (x <= x_pre)) (PreH7 : (0 <= mn)) (PreH8 : (mn <= 9)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx )) (PreH12 : (x <> 0)) ,
  (0 <= (x ÷ 10 ))
.

Definition step_entail_wit_2_3 := 
(
forall (x_pre: Z) (mx: Z) (mn: Z) (x: Z) (PreH1 : ((signed_last_nbits ((x % ( 10 ) )) (32)) <= mx)) (PreH2 : ((signed_last_nbits ((x % ( 10 ) )) (32)) < mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : (0 <= x)) (PreH6 : (x <= x_pre)) (PreH7 : (0 <= mn)) (PreH8 : (mn <= 9)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx )) (PreH12 : (x <> 0)) ,
  TT && emp 
|--
  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= 1810000000000000000) ” 
  &&  “ (0 <= (x ÷ 10 )) ” 
  &&  “ ((x ÷ 10 ) <= x_pre) ” 
  &&  “ (0 <= (signed_last_nbits ((x % ( 10 ) )) (32))) ” 
  &&  “ ((signed_last_nbits ((x % ( 10 ) )) (32)) <= 9) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 9) ” 
  &&  “ (DigitScanState x_pre (x ÷ 10 ) (signed_last_nbits ((x % ( 10 ) )) (32)) mx ) ”
  &&  emp
) \/
(
forall (x_pre: Z) (mx: Z) (mn: Z) (x: Z) (PreH1 : ((signed_last_nbits ((x % ( 10 ) )) (32)) <= mx)) (PreH2 : ((signed_last_nbits ((x % ( 10 ) )) (32)) < mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : (0 <= x)) (PreH6 : (x <= x_pre)) (PreH7 : (0 <= mn)) (PreH8 : (mn <= 9)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx )) (PreH12 : (x <> 0)) ,
  TT && emp 
|--
  “ (DigitScanState x_pre (x ÷ 10 ) (signed_last_nbits ((x % ( 10 ) )) (32)) mx ) ” 
  &&  “ (0 <= (signed_last_nbits ((x % ( 10 ) )) (32))) ” 
  &&  “ ((x ÷ 10 ) <= x_pre) ” 
  &&  “ (0 <= (x ÷ 10 )) ”
  &&  emp
).

Definition step_entail_wit_2_3_split_goal_1 := 
forall (x_pre: Z) (mx: Z) (mn: Z) (x: Z) (PreH1 : ((signed_last_nbits ((x % ( 10 ) )) (32)) <= mx)) (PreH2 : ((signed_last_nbits ((x % ( 10 ) )) (32)) < mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : (0 <= x)) (PreH6 : (x <= x_pre)) (PreH7 : (0 <= mn)) (PreH8 : (mn <= 9)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx )) (PreH12 : (x <> 0)) ,
  (DigitScanState x_pre (x ÷ 10 ) (signed_last_nbits ((x % ( 10 ) )) (32)) mx )
.

Definition step_entail_wit_2_3_split_goal_2 := 
forall (x_pre: Z) (mx: Z) (mn: Z) (x: Z) (PreH1 : ((signed_last_nbits ((x % ( 10 ) )) (32)) <= mx)) (PreH2 : ((signed_last_nbits ((x % ( 10 ) )) (32)) < mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : (0 <= x)) (PreH6 : (x <= x_pre)) (PreH7 : (0 <= mn)) (PreH8 : (mn <= 9)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx )) (PreH12 : (x <> 0)) ,
  (0 <= (signed_last_nbits ((x % ( 10 ) )) (32)))
.

Definition step_entail_wit_2_3_split_goal_3 := 
forall (x_pre: Z) (mx: Z) (mn: Z) (x: Z) (PreH1 : ((signed_last_nbits ((x % ( 10 ) )) (32)) <= mx)) (PreH2 : ((signed_last_nbits ((x % ( 10 ) )) (32)) < mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : (0 <= x)) (PreH6 : (x <= x_pre)) (PreH7 : (0 <= mn)) (PreH8 : (mn <= 9)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx )) (PreH12 : (x <> 0)) ,
  ((x ÷ 10 ) <= x_pre)
.

Definition step_entail_wit_2_3_split_goal_4 := 
forall (x_pre: Z) (mx: Z) (mn: Z) (x: Z) (PreH1 : ((signed_last_nbits ((x % ( 10 ) )) (32)) <= mx)) (PreH2 : ((signed_last_nbits ((x % ( 10 ) )) (32)) < mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : (0 <= x)) (PreH6 : (x <= x_pre)) (PreH7 : (0 <= mn)) (PreH8 : (mn <= 9)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx )) (PreH12 : (x <> 0)) ,
  (0 <= (x ÷ 10 ))
.

Definition step_entail_wit_2_4 := 
(
forall (x_pre: Z) (mx: Z) (mn: Z) (x: Z) (PreH1 : ((signed_last_nbits ((x % ( 10 ) )) (32)) <= mx)) (PreH2 : ((signed_last_nbits ((x % ( 10 ) )) (32)) >= mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : (0 <= x)) (PreH6 : (x <= x_pre)) (PreH7 : (0 <= mn)) (PreH8 : (mn <= 9)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx )) (PreH12 : (x <> 0)) ,
  TT && emp 
|--
  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= 1810000000000000000) ” 
  &&  “ (0 <= (x ÷ 10 )) ” 
  &&  “ ((x ÷ 10 ) <= x_pre) ” 
  &&  “ (0 <= mn) ” 
  &&  “ (mn <= 9) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= 9) ” 
  &&  “ (DigitScanState x_pre (x ÷ 10 ) mn mx ) ”
  &&  emp
) \/
(
forall (x_pre: Z) (mx: Z) (mn: Z) (x: Z) (PreH1 : ((signed_last_nbits ((x % ( 10 ) )) (32)) <= mx)) (PreH2 : ((signed_last_nbits ((x % ( 10 ) )) (32)) >= mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : (0 <= x)) (PreH6 : (x <= x_pre)) (PreH7 : (0 <= mn)) (PreH8 : (mn <= 9)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx )) (PreH12 : (x <> 0)) ,
  TT && emp 
|--
  “ (DigitScanState x_pre (x ÷ 10 ) mn mx ) ” 
  &&  “ ((x ÷ 10 ) <= x_pre) ” 
  &&  “ (0 <= (x ÷ 10 )) ”
  &&  emp
).

Definition step_entail_wit_2_4_split_goal_1 := 
forall (x_pre: Z) (mx: Z) (mn: Z) (x: Z) (PreH1 : ((signed_last_nbits ((x % ( 10 ) )) (32)) <= mx)) (PreH2 : ((signed_last_nbits ((x % ( 10 ) )) (32)) >= mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : (0 <= x)) (PreH6 : (x <= x_pre)) (PreH7 : (0 <= mn)) (PreH8 : (mn <= 9)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx )) (PreH12 : (x <> 0)) ,
  (DigitScanState x_pre (x ÷ 10 ) mn mx )
.

Definition step_entail_wit_2_4_split_goal_2 := 
forall (x_pre: Z) (mx: Z) (mn: Z) (x: Z) (PreH1 : ((signed_last_nbits ((x % ( 10 ) )) (32)) <= mx)) (PreH2 : ((signed_last_nbits ((x % ( 10 ) )) (32)) >= mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : (0 <= x)) (PreH6 : (x <= x_pre)) (PreH7 : (0 <= mn)) (PreH8 : (mn <= 9)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx )) (PreH12 : (x <> 0)) ,
  ((x ÷ 10 ) <= x_pre)
.

Definition step_entail_wit_2_4_split_goal_3 := 
forall (x_pre: Z) (mx: Z) (mn: Z) (x: Z) (PreH1 : ((signed_last_nbits ((x % ( 10 ) )) (32)) <= mx)) (PreH2 : ((signed_last_nbits ((x % ( 10 ) )) (32)) >= mn)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= 1810000000000000000)) (PreH5 : (0 <= x)) (PreH6 : (x <= x_pre)) (PreH7 : (0 <= mn)) (PreH8 : (mn <= 9)) (PreH9 : (0 <= mx)) (PreH10 : (mx <= 9)) (PreH11 : (DigitScanState x_pre x mn mx )) (PreH12 : (x <> 0)) ,
  (0 <= (x ÷ 10 ))
.

Definition step_return_wit_1 := 
(
forall (x_pre: Z) (mx: Z) (mn: Z) (x: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1810000000000000000)) (PreH3 : (0 <= x)) (PreH4 : (x <= x_pre)) (PreH5 : (0 <= mn)) (PreH6 : (mn <= 9)) (PreH7 : (0 <= mx)) (PreH8 : (mx <= 9)) (PreH9 : (DigitScanState x_pre x mn mx )) (PreH10 : (x = 0)) ,
  TT && emp 
|--
  “ (0 <= (mn * mx )) ” 
  &&  “ ((mn * mx ) <= 81) ” 
  &&  “ (DigitRecurrenceStep x_pre (x_pre + (mn * mx ) ) ) ”
  &&  emp
) \/
(
forall (x_pre: Z) (mx: Z) (mn: Z) (x: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1810000000000000000)) (PreH3 : (0 <= x)) (PreH4 : (x <= x_pre)) (PreH5 : (0 <= mn)) (PreH6 : (mn <= 9)) (PreH7 : (0 <= mx)) (PreH8 : (mx <= 9)) (PreH9 : (DigitScanState x_pre x mn mx )) (PreH10 : (x = 0)) ,
  TT && emp 
|--
  “ (DigitRecurrenceStep x_pre (x_pre + (mn * mx ) ) ) ”
  &&  emp
).

Definition step_return_wit_1_split_goal_1 := 
forall (x_pre: Z) (mx: Z) (mn: Z) (x: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1810000000000000000)) (PreH3 : (0 <= x)) (PreH4 : (x <= x_pre)) (PreH5 : (0 <= mn)) (PreH6 : (mn <= 9)) (PreH7 : (0 <= mx)) (PreH8 : (mx <= 9)) (PreH9 : (DigitScanState x_pre x mn mx )) (PreH10 : (x = 0)) ,
  (DigitRecurrenceStep x_pre (x_pre + (mn * mx ) ) )
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (k_pre: Z) (a_pre: Z) (a1: Z) (PreH1 : (1 <= a1)) (PreH2 : (a1 <= 1000000000000000000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 10000000000000000)) (PreH5 : (a_pre = a1)) ,
  ((( &( "i" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_2 := 
forall (k_pre: Z) (a_pre: Z) (a1: Z) (a: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 81)) (PreH4 : (DigitRecurrenceStep a (a + retval ) )) (PreH5 : (i < k_pre)) (PreH6 : (a_pre = a1)) (PreH7 : (1 <= a1)) (PreH8 : (a1 <= 1000000000000000000)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 10000000000000000)) (PreH11 : (1 <= i)) (PreH12 : (i <= k_pre)) (PreH13 : (a1 <= a)) (PreH14 : (a <= (a1 + (81 * (i - 1 ) ) ))) (PreH15 : (a <= 1810000000000000000)) (PreH16 : (SequencePrefix a1 i a )) ,
  ((( &( "add" ) )) # Int64  |-> retval)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "i" ) )) # Int64  |-> i)
  **  ((( &( "a" ) )) # Int64  |-> a)
|--
  “ ((a + retval ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (a + retval )) ”
.

Definition solver_safety_wit_3 := 
forall (k_pre: Z) (a_pre: Z) (a1: Z) (a: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 81)) (PreH4 : (DigitRecurrenceStep a (a + retval ) )) (PreH5 : (i < k_pre)) (PreH6 : (a_pre = a1)) (PreH7 : (1 <= a1)) (PreH8 : (a1 <= 1000000000000000000)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 10000000000000000)) (PreH11 : (1 <= i)) (PreH12 : (i <= k_pre)) (PreH13 : (a1 <= a)) (PreH14 : (a <= (a1 + (81 * (i - 1 ) ) ))) (PreH15 : (a <= 1810000000000000000)) (PreH16 : (SequencePrefix a1 i a )) ,
  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "i" ) )) # Int64  |-> i)
  **  ((( &( "a" ) )) # Int64  |-> (a + retval ))
|--
  “ ((i + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (k_pre: Z) (a_pre: Z) (a1: Z) (PreH1 : (1 <= a1)) (PreH2 : (a1 <= 1000000000000000000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 10000000000000000)) (PreH5 : (a_pre = a1)) ,
  TT && emp 
|--
  “ (a_pre = a1) ” 
  &&  “ (1 <= a1) ” 
  &&  “ (a1 <= 1000000000000000000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 10000000000000000) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (a1 <= a_pre) ” 
  &&  “ (a_pre <= (a1 + (81 * (1 - 1 ) ) )) ” 
  &&  “ (a_pre <= 1810000000000000000) ” 
  &&  “ (SequencePrefix a1 1 a_pre ) ”
  &&  emp
) \/
(
forall (k_pre: Z) (a_pre: Z) (a1: Z) (PreH1 : (1 <= a1)) (PreH2 : (a1 <= 1000000000000000000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 10000000000000000)) (PreH5 : (a_pre = a1)) ,
  TT && emp 
|--
  “ (SequencePrefix a_pre 1 a_pre ) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (k_pre: Z) (a_pre: Z) (a1: Z) (PreH1 : (1 <= a1)) (PreH2 : (a1 <= 1000000000000000000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 10000000000000000)) (PreH5 : (a_pre = a1)) ,
  (SequencePrefix a_pre 1 a_pre )
.

Definition solver_entail_wit_2 := 
(
forall (k_pre: Z) (a_pre: Z) (a1: Z) (a: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 81)) (PreH4 : (DigitRecurrenceStep a (a + retval ) )) (PreH5 : (i < k_pre)) (PreH6 : (a_pre = a1)) (PreH7 : (1 <= a1)) (PreH8 : (a1 <= 1000000000000000000)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 10000000000000000)) (PreH11 : (1 <= i)) (PreH12 : (i <= k_pre)) (PreH13 : (a1 <= a)) (PreH14 : (a <= (a1 + (81 * (i - 1 ) ) ))) (PreH15 : (a <= 1810000000000000000)) (PreH16 : (SequencePrefix a1 i a )) ,
  TT && emp 
|--
  “ (a_pre = a1) ” 
  &&  “ (1 <= a1) ” 
  &&  “ (a1 <= 1000000000000000000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 10000000000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < k_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (a1 <= a) ” 
  &&  “ (a <= (a1 + (81 * (i - 1 ) ) )) ” 
  &&  “ (a <= 1810000000000000000) ” 
  &&  “ (SequencePrefix a1 i a ) ” 
  &&  “ (Spec a1 k_pre a ) ”
  &&  emp
) \/
(
forall (k_pre: Z) (a_pre: Z) (a1: Z) (a: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 81)) (PreH4 : (DigitRecurrenceStep a (a + retval ) )) (PreH5 : (i < k_pre)) (PreH6 : (a_pre = a1)) (PreH7 : (1 <= a1)) (PreH8 : (a1 <= 1000000000000000000)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 10000000000000000)) (PreH11 : (1 <= i)) (PreH12 : (i <= k_pre)) (PreH13 : (a1 <= a)) (PreH14 : (a <= (a1 + (81 * (i - 1 ) ) ))) (PreH15 : (a <= 1810000000000000000)) (PreH16 : (SequencePrefix a1 i a )) ,
  TT && emp 
|--
  “ (Spec a_pre k_pre a ) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (k_pre: Z) (a_pre: Z) (a1: Z) (a: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 81)) (PreH4 : (DigitRecurrenceStep a (a + retval ) )) (PreH5 : (i < k_pre)) (PreH6 : (a_pre = a1)) (PreH7 : (1 <= a1)) (PreH8 : (a1 <= 1000000000000000000)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 10000000000000000)) (PreH11 : (1 <= i)) (PreH12 : (i <= k_pre)) (PreH13 : (a1 <= a)) (PreH14 : (a <= (a1 + (81 * (i - 1 ) ) ))) (PreH15 : (a <= 1810000000000000000)) (PreH16 : (SequencePrefix a1 i a )) ,
  (Spec a_pre k_pre a )
.

Definition solver_entail_wit_3 := 
(
forall (k_pre: Z) (a_pre: Z) (a1: Z) (a: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 81)) (PreH4 : (DigitRecurrenceStep a (a + retval ) )) (PreH5 : (i < k_pre)) (PreH6 : (a_pre = a1)) (PreH7 : (1 <= a1)) (PreH8 : (a1 <= 1000000000000000000)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 10000000000000000)) (PreH11 : (1 <= i)) (PreH12 : (i <= k_pre)) (PreH13 : (a1 <= a)) (PreH14 : (a <= (a1 + (81 * (i - 1 ) ) ))) (PreH15 : (a <= 1810000000000000000)) (PreH16 : (SequencePrefix a1 i a )) ,
  TT && emp 
|--
  “ (a_pre = a1) ” 
  &&  “ (1 <= a1) ” 
  &&  “ (a1 <= 1000000000000000000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 10000000000000000) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= k_pre) ” 
  &&  “ (a1 <= (a + retval )) ” 
  &&  “ ((a + retval ) <= (a1 + (81 * ((i + 1 ) - 1 ) ) )) ” 
  &&  “ ((a + retval ) <= 1810000000000000000) ” 
  &&  “ (SequencePrefix a1 (i + 1 ) (a + retval ) ) ”
  &&  emp
) \/
(
forall (k_pre: Z) (a_pre: Z) (a1: Z) (a: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 81)) (PreH4 : (DigitRecurrenceStep a (a + retval ) )) (PreH5 : (i < k_pre)) (PreH6 : (a_pre = a1)) (PreH7 : (1 <= a1)) (PreH8 : (a1 <= 1000000000000000000)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 10000000000000000)) (PreH11 : (1 <= i)) (PreH12 : (i <= k_pre)) (PreH13 : (a1 <= a)) (PreH14 : (a <= (a1 + (81 * (i - 1 ) ) ))) (PreH15 : (a <= 1810000000000000000)) (PreH16 : (SequencePrefix a1 i a )) ,
  TT && emp 
|--
  “ (SequencePrefix a_pre (i + 1 ) (a + retval ) ) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 := 
forall (k_pre: Z) (a_pre: Z) (a1: Z) (a: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 81)) (PreH4 : (DigitRecurrenceStep a (a + retval ) )) (PreH5 : (i < k_pre)) (PreH6 : (a_pre = a1)) (PreH7 : (1 <= a1)) (PreH8 : (a1 <= 1000000000000000000)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 10000000000000000)) (PreH11 : (1 <= i)) (PreH12 : (i <= k_pre)) (PreH13 : (a1 <= a)) (PreH14 : (a <= (a1 + (81 * (i - 1 ) ) ))) (PreH15 : (a <= 1810000000000000000)) (PreH16 : (SequencePrefix a1 i a )) ,
  (SequencePrefix a_pre (i + 1 ) (a + retval ) )
.

Definition solver_return_wit_1 := 
(
forall (k_pre: Z) (a_pre: Z) (a1: Z) (a: Z) (i: Z) (PreH1 : (i >= k_pre)) (PreH2 : (a_pre = a1)) (PreH3 : (1 <= a1)) (PreH4 : (a1 <= 1000000000000000000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 10000000000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= k_pre)) (PreH9 : (a1 <= a)) (PreH10 : (a <= (a1 + (81 * (i - 1 ) ) ))) (PreH11 : (a <= 1810000000000000000)) (PreH12 : (SequencePrefix a1 i a )) ,
  TT && emp 
|--
  “ (Spec a1 k_pre a ) ”
  &&  emp
) \/
(
forall (k_pre: Z) (a_pre: Z) (a1: Z) (a: Z) (i: Z) (PreH1 : (i >= k_pre)) (PreH2 : (a_pre = a1)) (PreH3 : (1 <= a1)) (PreH4 : (a1 <= 1000000000000000000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 10000000000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= k_pre)) (PreH9 : (a1 <= a)) (PreH10 : (a <= (a1 + (81 * (i - 1 ) ) ))) (PreH11 : (a <= 1810000000000000000)) (PreH12 : (SequencePrefix a1 i a )) ,
  TT && emp 
|--
  “ (Spec a_pre k_pre a ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 := 
forall (k_pre: Z) (a_pre: Z) (a1: Z) (a: Z) (i: Z) (PreH1 : (i >= k_pre)) (PreH2 : (a_pre = a1)) (PreH3 : (1 <= a1)) (PreH4 : (a1 <= 1000000000000000000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 10000000000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= k_pre)) (PreH9 : (a1 <= a)) (PreH10 : (a <= (a1 + (81 * (i - 1 ) ) ))) (PreH11 : (a <= 1810000000000000000)) (PreH12 : (SequencePrefix a1 i a )) ,
  (Spec a_pre k_pre a )
.

Definition solver_return_wit_2 := 
forall (k_pre: Z) (a_pre: Z) (a1: Z) (i: Z) (add: Z) (a: Z) (PreH1 : (a_pre = a1)) (PreH2 : (1 <= a1)) (PreH3 : (a1 <= 1000000000000000000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 10000000000000000)) (PreH6 : (1 <= i)) (PreH7 : (i < k_pre)) (PreH8 : (add = 0)) (PreH9 : (a1 <= a)) (PreH10 : (a <= (a1 + (81 * (i - 1 ) ) ))) (PreH11 : (a <= 1810000000000000000)) (PreH12 : (SequencePrefix a1 i a )) (PreH13 : (Spec a1 k_pre a )) ,
  TT && emp 
|--
  “ (Spec a1 k_pre a ) ”
  &&  emp
.

Definition solver_partial_solve_wit_1_pure := 
forall (k_pre: Z) (a_pre: Z) (a1: Z) (a: Z) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (a_pre = a1)) (PreH3 : (1 <= a1)) (PreH4 : (a1 <= 1000000000000000000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 10000000000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= k_pre)) (PreH9 : (a1 <= a)) (PreH10 : (a <= (a1 + (81 * (i - 1 ) ) ))) (PreH11 : (a <= 1810000000000000000)) (PreH12 : (SequencePrefix a1 i a )) ,
  ((( &( "add" ) )) # Int64  |->_)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "i" ) )) # Int64  |-> i)
  **  ((( &( "a" ) )) # Int64  |-> a)
|--
  “ (1 <= a) ” 
  &&  “ (a <= 1810000000000000000) ”
.

Definition solver_partial_solve_wit_1_aux := 
forall (k_pre: Z) (a_pre: Z) (a1: Z) (a: Z) (i: Z) (PreH1 : (i < k_pre)) (PreH2 : (a_pre = a1)) (PreH3 : (1 <= a1)) (PreH4 : (a1 <= 1000000000000000000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 10000000000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= k_pre)) (PreH9 : (a1 <= a)) (PreH10 : (a <= (a1 + (81 * (i - 1 ) ) ))) (PreH11 : (a <= 1810000000000000000)) (PreH12 : (SequencePrefix a1 i a )) ,
  TT && emp 
|--
  “ (1 <= a) ” 
  &&  “ (a <= 1810000000000000000) ” 
  &&  “ (i < k_pre) ” 
  &&  “ (a_pre = a1) ” 
  &&  “ (1 <= a1) ” 
  &&  “ (a1 <= 1000000000000000000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 10000000000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= k_pre) ” 
  &&  “ (a1 <= a) ” 
  &&  “ (a <= (a1 + (81 * (i - 1 ) ) )) ” 
  &&  “ (a <= 1810000000000000000) ” 
  &&  “ (SequencePrefix a1 i a ) ”
  &&  emp
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Module Type VC_Correct.


Axiom proof_of_step_safety_wit_1 : step_safety_wit_1.
Axiom proof_of_step_safety_wit_2 : step_safety_wit_2.
Axiom proof_of_step_safety_wit_3 : step_safety_wit_3.
Axiom proof_of_step_safety_wit_4 : step_safety_wit_4.
Axiom proof_of_step_safety_wit_5 : step_safety_wit_5.
Axiom proof_of_step_safety_wit_6 : step_safety_wit_6.
Axiom proof_of_step_safety_wit_7 : step_safety_wit_7.
Axiom proof_of_step_entail_wit_1 : step_entail_wit_1.
Axiom proof_of_step_entail_wit_2_1 : step_entail_wit_2_1.
Axiom proof_of_step_entail_wit_2_2 : step_entail_wit_2_2.
Axiom proof_of_step_entail_wit_2_3 : step_entail_wit_2_3.
Axiom proof_of_step_entail_wit_2_4 : step_entail_wit_2_4.
Axiom proof_of_step_return_wit_1 : step_return_wit_1.
Axiom proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Axiom proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Axiom proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.

End VC_Correct.
