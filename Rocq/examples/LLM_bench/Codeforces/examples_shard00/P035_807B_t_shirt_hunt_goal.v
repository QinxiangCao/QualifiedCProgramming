From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P035_807B_t_shirt_hunt_lib.
Local Open Scope sac.

(*----- Function wins -----*)

Definition wins_safety_wit_1 :=
forall (place_pre: Z) (score_pre: Z) (PreH1 : (26 <= place_pre)) (PreH2 : (place_pre <= 500)) (PreH3 : (0 <= score_pre)) (PreH4 : (score_pre <= INT_MAX)),
  ((( &( "z" ) )) # Int  |->_)
  **  ((( &( "place" ) )) # Int  |-> place_pre)
  **  ((( &( "score" ) )) # Int  |-> score_pre)
|--
  “ (((score_pre ÷ 50 ) <> (INT_MIN)) \/ (475 <> (-1))) ”
  &&  “ (475 <> 0) ”
.

Definition wins_safety_wit_2 :=
forall (place_pre: Z) (score_pre: Z) (PreH1 : (26 <= place_pre)) (PreH2 : (place_pre <= 500)) (PreH3 : (0 <= score_pre)) (PreH4 : (score_pre <= INT_MAX)),
  ((( &( "z" ) )) # Int  |->_)
  **  ((( &( "place" ) )) # Int  |-> place_pre)
  **  ((( &( "score" ) )) # Int  |-> score_pre)
|--
  “ ((score_pre <> (INT_MIN)) \/ (50 <> (-1))) ”
  &&  “ (50 <> 0) ”
.

Definition wins_safety_wit_3 :=
forall (place_pre: Z) (score_pre: Z) (PreH1 : (26 <= place_pre)) (PreH2 : (place_pre <= 500)) (PreH3 : (0 <= score_pre)) (PreH4 : (score_pre <= INT_MAX)),
  ((( &( "z" ) )) # Int  |->_)
  **  ((( &( "place" ) )) # Int  |-> place_pre)
  **  ((( &( "score" ) )) # Int  |-> score_pre)
|--
  “ (50 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 50) ”
.

Definition wins_safety_wit_4 :=
forall (place_pre: Z) (score_pre: Z) (PreH1 : (26 <= place_pre)) (PreH2 : (place_pre <= 500)) (PreH3 : (0 <= score_pre)) (PreH4 : (score_pre <= INT_MAX)),
  ((( &( "z" ) )) # Int  |->_)
  **  ((( &( "place" ) )) # Int  |-> place_pre)
  **  ((( &( "score" ) )) # Int  |-> score_pre)
|--
  “ (475 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 475) ”
.

Definition wins_safety_wit_5 :=
forall (place_pre: Z) (score_pre: Z) (PreH1 : (26 <= place_pre)) (PreH2 : (place_pre <= 500)) (PreH3 : (0 <= score_pre)) (PreH4 : (score_pre <= INT_MAX)),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "z" ) )) # Int  |-> ((score_pre ÷ 50 ) % ( 475 ) ))
  **  ((( &( "place" ) )) # Int  |-> place_pre)
  **  ((( &( "score" ) )) # Int  |-> score_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition wins_safety_wit_6 :=
forall (place_pre: Z) (score_pre: Z) (z: Z) (i: Z) (PreH1 : (26 <= place_pre)) (PreH2 : (place_pre <= 500)) (PreH3 : (0 <= score_pre)) (PreH4 : (score_pre <= INT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i <= 25)) (PreH7 : (0 <= z)) (PreH8 : (z < 475)) (PreH9 : (ShirtScanState score_pre place_pre i z )),
  ((( &( "place" ) )) # Int  |-> place_pre)
  **  ((( &( "score" ) )) # Int  |-> score_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "z" ) )) # Int  |-> z)
|--
  “ (25 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 25) ”
.

Definition wins_safety_wit_7 :=
forall (place_pre: Z) (score_pre: Z) (z: Z) (i: Z) (PreH1 : (i < 25)) (PreH2 : (26 <= place_pre)) (PreH3 : (place_pre <= 500)) (PreH4 : (0 <= score_pre)) (PreH5 : (score_pre <= INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= 25)) (PreH8 : (0 <= z)) (PreH9 : (z < 475)) (PreH10 : (ShirtScanState score_pre place_pre i z )),
  ((( &( "place" ) )) # Int  |-> place_pre)
  **  ((( &( "score" ) )) # Int  |-> score_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "z" ) )) # Int  |-> z)
|--
  “ ((((z * 96 ) + 42 ) <> (INT_MIN)) \/ (475 <> (-1))) ”
  &&  “ (475 <> 0) ”
.

Definition wins_safety_wit_8 :=
forall (place_pre: Z) (score_pre: Z) (z: Z) (i: Z) (PreH1 : (i < 25)) (PreH2 : (26 <= place_pre)) (PreH3 : (place_pre <= 500)) (PreH4 : (0 <= score_pre)) (PreH5 : (score_pre <= INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= 25)) (PreH8 : (0 <= z)) (PreH9 : (z < 475)) (PreH10 : (ShirtScanState score_pre place_pre i z )),
  ((( &( "place" ) )) # Int  |-> place_pre)
  **  ((( &( "score" ) )) # Int  |-> score_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "z" ) )) # Int  |-> z)
|--
  “ (((z * 96 ) + 42 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((z * 96 ) + 42 )) ”
.

Definition wins_safety_wit_9 :=
forall (place_pre: Z) (score_pre: Z) (z: Z) (i: Z) (PreH1 : (i < 25)) (PreH2 : (26 <= place_pre)) (PreH3 : (place_pre <= 500)) (PreH4 : (0 <= score_pre)) (PreH5 : (score_pre <= INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= 25)) (PreH8 : (0 <= z)) (PreH9 : (z < 475)) (PreH10 : (ShirtScanState score_pre place_pre i z )),
  ((( &( "place" ) )) # Int  |-> place_pre)
  **  ((( &( "score" ) )) # Int  |-> score_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "z" ) )) # Int  |-> z)
|--
  “ ((z * 96 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (z * 96 )) ”
.

Definition wins_safety_wit_10 :=
forall (place_pre: Z) (score_pre: Z) (z: Z) (i: Z) (PreH1 : (i < 25)) (PreH2 : (26 <= place_pre)) (PreH3 : (place_pre <= 500)) (PreH4 : (0 <= score_pre)) (PreH5 : (score_pre <= INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= 25)) (PreH8 : (0 <= z)) (PreH9 : (z < 475)) (PreH10 : (ShirtScanState score_pre place_pre i z )),
  ((( &( "place" ) )) # Int  |-> place_pre)
  **  ((( &( "score" ) )) # Int  |-> score_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "z" ) )) # Int  |-> z)
|--
  “ (96 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 96) ”
.

Definition wins_safety_wit_11 :=
forall (place_pre: Z) (score_pre: Z) (z: Z) (i: Z) (PreH1 : (i < 25)) (PreH2 : (26 <= place_pre)) (PreH3 : (place_pre <= 500)) (PreH4 : (0 <= score_pre)) (PreH5 : (score_pre <= INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= 25)) (PreH8 : (0 <= z)) (PreH9 : (z < 475)) (PreH10 : (ShirtScanState score_pre place_pre i z )),
  ((( &( "place" ) )) # Int  |-> place_pre)
  **  ((( &( "score" ) )) # Int  |-> score_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "z" ) )) # Int  |-> z)
|--
  “ (42 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 42) ”
.

Definition wins_safety_wit_12 :=
forall (place_pre: Z) (score_pre: Z) (z: Z) (i: Z) (PreH1 : (i < 25)) (PreH2 : (26 <= place_pre)) (PreH3 : (place_pre <= 500)) (PreH4 : (0 <= score_pre)) (PreH5 : (score_pre <= INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= 25)) (PreH8 : (0 <= z)) (PreH9 : (z < 475)) (PreH10 : (ShirtScanState score_pre place_pre i z )),
  ((( &( "place" ) )) # Int  |-> place_pre)
  **  ((( &( "score" ) )) # Int  |-> score_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "z" ) )) # Int  |-> z)
|--
  “ (475 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 475) ”
.

Definition wins_safety_wit_13 :=
(
forall (place_pre: Z) (score_pre: Z) (z: Z) (i: Z) (PreH1 : (i < 25)) (PreH2 : (26 <= place_pre)) (PreH3 : (place_pre <= 500)) (PreH4 : (0 <= score_pre)) (PreH5 : (score_pre <= INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= 25)) (PreH8 : (0 <= z)) (PreH9 : (z < 475)) (PreH10 : (ShirtScanState score_pre place_pre i z )),
  ((( &( "place" ) )) # Int  |-> place_pre)
  **  ((( &( "score" ) )) # Int  |-> score_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "z" ) )) # Int  |-> (((z * 96 ) + 42 ) % ( 475 ) ))
|--
  “ (((((z * 96 ) + 42 ) % ( 475 ) ) + 26 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((((z * 96 ) + 42 ) % ( 475 ) ) + 26 )) ”
) \/
(
forall (place_pre: Z) (score_pre: Z) (z: Z) (i: Z) (PreH1 : (i < 25)) (PreH2 : (26 <= place_pre)) (PreH3 : (place_pre <= 500)) (PreH4 : (0 <= score_pre)) (PreH5 : (score_pre <= INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= 25)) (PreH8 : (0 <= z)) (PreH9 : (z < 475)) (PreH10 : (ShirtScanState score_pre place_pre i z )),
  ((( &( "place" ) )) # Int  |-> place_pre)
  **  ((( &( "score" ) )) # Int  |-> score_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "z" ) )) # Int  |-> (((z * 96 ) + 42 ) % ( 475 ) ))
|--
  “ (((((z * 96 ) + 42 ) % ( 475 ) ) + 26 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((((z * 96 ) + 42 ) % ( 475 ) ) + 26 )) ”
).

Definition wins_safety_wit_13_split_goal_1 :=
forall (place_pre: Z) (score_pre: Z) (z: Z) (i: Z) (PreH1 : (i < 25)) (PreH2 : (26 <= place_pre)) (PreH3 : (place_pre <= 500)) (PreH4 : (0 <= score_pre)) (PreH5 : (score_pre <= INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= 25)) (PreH8 : (0 <= z)) (PreH9 : (z < 475)) (PreH10 : (ShirtScanState score_pre place_pre i z )),
  ((( &( "place" ) )) # Int  |-> place_pre)
  **  ((( &( "score" ) )) # Int  |-> score_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "z" ) )) # Int  |-> (((z * 96 ) + 42 ) % ( 475 ) ))
|--
  “ (((((z * 96 ) + 42 ) % ( 475 ) ) + 26 ) <= INT_MAX) ”
.

Definition wins_safety_wit_13_split_goal_2 :=
forall (place_pre: Z) (score_pre: Z) (z: Z) (i: Z) (PreH1 : (i < 25)) (PreH2 : (26 <= place_pre)) (PreH3 : (place_pre <= 500)) (PreH4 : (0 <= score_pre)) (PreH5 : (score_pre <= INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= 25)) (PreH8 : (0 <= z)) (PreH9 : (z < 475)) (PreH10 : (ShirtScanState score_pre place_pre i z )),
  ((( &( "place" ) )) # Int  |-> place_pre)
  **  ((( &( "score" ) )) # Int  |-> score_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "z" ) )) # Int  |-> (((z * 96 ) + 42 ) % ( 475 ) ))
|--
  “ ((INT_MIN) <= ((((z * 96 ) + 42 ) % ( 475 ) ) + 26 )) ”
.

Definition wins_safety_wit_14 :=
forall (place_pre: Z) (score_pre: Z) (z: Z) (i: Z) (PreH1 : (i < 25)) (PreH2 : (26 <= place_pre)) (PreH3 : (place_pre <= 500)) (PreH4 : (0 <= score_pre)) (PreH5 : (score_pre <= INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= 25)) (PreH8 : (0 <= z)) (PreH9 : (z < 475)) (PreH10 : (ShirtScanState score_pre place_pre i z )),
  ((( &( "place" ) )) # Int  |-> place_pre)
  **  ((( &( "score" ) )) # Int  |-> score_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "z" ) )) # Int  |-> (((z * 96 ) + 42 ) % ( 475 ) ))
|--
  “ (26 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 26) ”
.

Definition wins_safety_wit_15 :=
forall (place_pre: Z) (score_pre: Z) (z: Z) (i: Z) (PreH1 : (((((z * 96 ) + 42 ) % ( 475 ) ) + 26 ) = place_pre)) (PreH2 : (i < 25)) (PreH3 : (26 <= place_pre)) (PreH4 : (place_pre <= 500)) (PreH5 : (0 <= score_pre)) (PreH6 : (score_pre <= INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= 25)) (PreH9 : (0 <= z)) (PreH10 : (z < 475)) (PreH11 : (ShirtScanState score_pre place_pre i z )),
  ((( &( "place" ) )) # Int  |-> place_pre)
  **  ((( &( "score" ) )) # Int  |-> score_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "z" ) )) # Int  |-> (((z * 96 ) + 42 ) % ( 475 ) ))
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition wins_safety_wit_16 :=
forall (place_pre: Z) (score_pre: Z) (z: Z) (i: Z) (PreH1 : (((((z * 96 ) + 42 ) % ( 475 ) ) + 26 ) <> place_pre)) (PreH2 : (i < 25)) (PreH3 : (26 <= place_pre)) (PreH4 : (place_pre <= 500)) (PreH5 : (0 <= score_pre)) (PreH6 : (score_pre <= INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= 25)) (PreH9 : (0 <= z)) (PreH10 : (z < 475)) (PreH11 : (ShirtScanState score_pre place_pre i z )),
  ((( &( "place" ) )) # Int  |-> place_pre)
  **  ((( &( "score" ) )) # Int  |-> score_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "z" ) )) # Int  |-> (((z * 96 ) + 42 ) % ( 475 ) ))
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition wins_safety_wit_17 :=
forall (place_pre: Z) (score_pre: Z) (z: Z) (i: Z) (PreH1 : (i >= 25)) (PreH2 : (26 <= place_pre)) (PreH3 : (place_pre <= 500)) (PreH4 : (0 <= score_pre)) (PreH5 : (score_pre <= INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= 25)) (PreH8 : (0 <= z)) (PreH9 : (z < 475)) (PreH10 : (ShirtScanState score_pre place_pre i z )),
  ((( &( "place" ) )) # Int  |-> place_pre)
  **  ((( &( "score" ) )) # Int  |-> score_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition wins_entail_wit_1 :=
(
forall (place_pre: Z) (score_pre: Z) (PreH1 : (26 <= place_pre)) (PreH2 : (place_pre <= 500)) (PreH3 : (0 <= score_pre)) (PreH4 : (score_pre <= INT_MAX)),
  TT && emp 
|--
  “ (26 <= place_pre) ”
  &&  “ (place_pre <= 500) ”
  &&  “ (0 <= score_pre) ”
  &&  “ (score_pre <= INT_MAX) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 25) ”
  &&  “ (0 <= ((score_pre ÷ 50 ) % ( 475 ) )) ”
  &&  “ (((score_pre ÷ 50 ) % ( 475 ) ) < 475) ”
  &&  “ (ShirtScanState score_pre place_pre 0 ((score_pre ÷ 50 ) % ( 475 ) ) ) ”
  &&  emp
) \/
(
forall (place_pre: Z) (score_pre: Z) (PreH1 : (26 <= place_pre)) (PreH2 : (place_pre <= 500)) (PreH3 : (0 <= score_pre)) (PreH4 : (score_pre <= INT_MAX)),
  TT && emp 
|--
  “ (ShirtScanState score_pre place_pre 0 ((score_pre ÷ 50 ) % ( 475 ) ) ) ”
  &&  “ (((score_pre ÷ 50 ) % ( 475 ) ) < 475) ”
  &&  “ (0 <= ((score_pre ÷ 50 ) % ( 475 ) )) ”
  &&  emp
).

Definition wins_entail_wit_1_split_goal_1 :=
forall (place_pre: Z) (score_pre: Z) (PreH1 : (26 <= place_pre)) (PreH2 : (place_pre <= 500)) (PreH3 : (0 <= score_pre)) (PreH4 : (score_pre <= INT_MAX)),
  (ShirtScanState score_pre place_pre 0 ((score_pre ÷ 50 ) % ( 475 ) ) )
.

Definition wins_entail_wit_1_split_goal_2 :=
forall (place_pre: Z) (score_pre: Z) (PreH1 : (26 <= place_pre)) (PreH2 : (place_pre <= 500)) (PreH3 : (0 <= score_pre)) (PreH4 : (score_pre <= INT_MAX)),
  (((score_pre ÷ 50 ) % ( 475 ) ) < 475)
.

Definition wins_entail_wit_1_split_goal_3 :=
forall (place_pre: Z) (score_pre: Z) (PreH1 : (26 <= place_pre)) (PreH2 : (place_pre <= 500)) (PreH3 : (0 <= score_pre)) (PreH4 : (score_pre <= INT_MAX)),
  (0 <= ((score_pre ÷ 50 ) % ( 475 ) ))
.

Definition wins_entail_wit_2 :=
(
forall (place_pre: Z) (score_pre: Z) (z: Z) (i: Z) (PreH1 : (((((z * 96 ) + 42 ) % ( 475 ) ) + 26 ) <> place_pre)) (PreH2 : (i < 25)) (PreH3 : (26 <= place_pre)) (PreH4 : (place_pre <= 500)) (PreH5 : (0 <= score_pre)) (PreH6 : (score_pre <= INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= 25)) (PreH9 : (0 <= z)) (PreH10 : (z < 475)) (PreH11 : (ShirtScanState score_pre place_pre i z )),
  TT && emp 
|--
  “ (26 <= place_pre) ”
  &&  “ (place_pre <= 500) ”
  &&  “ (0 <= score_pre) ”
  &&  “ (score_pre <= INT_MAX) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= 25) ”
  &&  “ (0 <= (((z * 96 ) + 42 ) % ( 475 ) )) ”
  &&  “ ((((z * 96 ) + 42 ) % ( 475 ) ) < 475) ”
  &&  “ (ShirtScanState score_pre place_pre (i + 1 ) (((z * 96 ) + 42 ) % ( 475 ) ) ) ”
  &&  emp
) \/
(
forall (place_pre: Z) (score_pre: Z) (z: Z) (i: Z) (PreH1 : (((((z * 96 ) + 42 ) % ( 475 ) ) + 26 ) <> place_pre)) (PreH2 : (i < 25)) (PreH3 : (26 <= place_pre)) (PreH4 : (place_pre <= 500)) (PreH5 : (0 <= score_pre)) (PreH6 : (score_pre <= INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= 25)) (PreH9 : (0 <= z)) (PreH10 : (z < 475)) (PreH11 : (ShirtScanState score_pre place_pre i z )),
  TT && emp 
|--
  “ (ShirtScanState score_pre place_pre (i + 1 ) (((z * 96 ) + 42 ) % ( 475 ) ) ) ”
  &&  “ ((((z * 96 ) + 42 ) % ( 475 ) ) < 475) ”
  &&  “ (0 <= (((z * 96 ) + 42 ) % ( 475 ) )) ”
  &&  emp
).

Definition wins_entail_wit_2_split_goal_1 :=
forall (place_pre: Z) (score_pre: Z) (z: Z) (i: Z) (PreH1 : (((((z * 96 ) + 42 ) % ( 475 ) ) + 26 ) <> place_pre)) (PreH2 : (i < 25)) (PreH3 : (26 <= place_pre)) (PreH4 : (place_pre <= 500)) (PreH5 : (0 <= score_pre)) (PreH6 : (score_pre <= INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= 25)) (PreH9 : (0 <= z)) (PreH10 : (z < 475)) (PreH11 : (ShirtScanState score_pre place_pre i z )),
  (ShirtScanState score_pre place_pre (i + 1 ) (((z * 96 ) + 42 ) % ( 475 ) ) )
.

Definition wins_entail_wit_2_split_goal_2 :=
forall (place_pre: Z) (score_pre: Z) (z: Z) (i: Z) (PreH1 : (((((z * 96 ) + 42 ) % ( 475 ) ) + 26 ) <> place_pre)) (PreH2 : (i < 25)) (PreH3 : (26 <= place_pre)) (PreH4 : (place_pre <= 500)) (PreH5 : (0 <= score_pre)) (PreH6 : (score_pre <= INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= 25)) (PreH9 : (0 <= z)) (PreH10 : (z < 475)) (PreH11 : (ShirtScanState score_pre place_pre i z )),
  ((((z * 96 ) + 42 ) % ( 475 ) ) < 475)
.

Definition wins_entail_wit_2_split_goal_3 :=
forall (place_pre: Z) (score_pre: Z) (z: Z) (i: Z) (PreH1 : (((((z * 96 ) + 42 ) % ( 475 ) ) + 26 ) <> place_pre)) (PreH2 : (i < 25)) (PreH3 : (26 <= place_pre)) (PreH4 : (place_pre <= 500)) (PreH5 : (0 <= score_pre)) (PreH6 : (score_pre <= INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= 25)) (PreH9 : (0 <= z)) (PreH10 : (z < 475)) (PreH11 : (ShirtScanState score_pre place_pre i z )),
  (0 <= (((z * 96 ) + 42 ) % ( 475 ) ))
.

Definition wins_return_wit_1 :=
(
forall (place_pre: Z) (score_pre: Z) (z: Z) (i: Z) (PreH1 : (i >= 25)) (PreH2 : (26 <= place_pre)) (PreH3 : (place_pre <= 500)) (PreH4 : (0 <= score_pre)) (PreH5 : (score_pre <= INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= 25)) (PreH8 : (0 <= z)) (PreH9 : (z < 475)) (PreH10 : (ShirtScanState score_pre place_pre i z )),
  TT && emp 
|--
  “ (0 = 0) ”
  &&  “ (NoShirtSelection score_pre place_pre ) ”
  &&  emp
) \/
(
forall (place_pre: Z) (score_pre: Z) (z: Z) (i: Z) (PreH1 : (i >= 25)) (PreH2 : (26 <= place_pre)) (PreH3 : (place_pre <= 500)) (PreH4 : (0 <= score_pre)) (PreH5 : (score_pre <= INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= 25)) (PreH8 : (0 <= z)) (PreH9 : (z < 475)) (PreH10 : (ShirtScanState score_pre place_pre i z )),
  TT && emp 
|--
  “ (NoShirtSelection score_pre place_pre ) ”
  &&  emp
).

Definition wins_return_wit_1_split_goal_1 :=
forall (place_pre: Z) (score_pre: Z) (z: Z) (i: Z) (PreH1 : (i >= 25)) (PreH2 : (26 <= place_pre)) (PreH3 : (place_pre <= 500)) (PreH4 : (0 <= score_pre)) (PreH5 : (score_pre <= INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= 25)) (PreH8 : (0 <= z)) (PreH9 : (z < 475)) (PreH10 : (ShirtScanState score_pre place_pre i z )),
  (NoShirtSelection score_pre place_pre )
.

Definition wins_return_wit_2 :=
(
forall (place_pre: Z) (score_pre: Z) (z: Z) (i: Z) (PreH1 : (((((z * 96 ) + 42 ) % ( 475 ) ) + 26 ) = place_pre)) (PreH2 : (i < 25)) (PreH3 : (26 <= place_pre)) (PreH4 : (place_pre <= 500)) (PreH5 : (0 <= score_pre)) (PreH6 : (score_pre <= INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= 25)) (PreH9 : (0 <= z)) (PreH10 : (z < 475)) (PreH11 : (ShirtScanState score_pre place_pre i z )),
  TT && emp 
|--
  “ (1 = 1) ”
  &&  “ (ShirtSelection score_pre place_pre ) ”
  &&  emp
) \/
(
forall (place_pre: Z) (score_pre: Z) (z: Z) (i: Z) (PreH1 : (((((z * 96 ) + 42 ) % ( 475 ) ) + 26 ) = place_pre)) (PreH2 : (i < 25)) (PreH3 : (26 <= place_pre)) (PreH4 : (place_pre <= 500)) (PreH5 : (0 <= score_pre)) (PreH6 : (score_pre <= INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= 25)) (PreH9 : (0 <= z)) (PreH10 : (z < 475)) (PreH11 : (ShirtScanState score_pre place_pre i z )),
  TT && emp 
|--
  “ (ShirtSelection score_pre ((((z * 96 ) + 42 ) % ( 475 ) ) + 26 ) ) ”
  &&  emp
).

Definition wins_return_wit_2_split_goal_1 :=
forall (place_pre: Z) (score_pre: Z) (z: Z) (i: Z) (PreH1 : (((((z * 96 ) + 42 ) % ( 475 ) ) + 26 ) = place_pre)) (PreH2 : (i < 25)) (PreH3 : (26 <= place_pre)) (PreH4 : (place_pre <= 500)) (PreH5 : (0 <= score_pre)) (PreH6 : (score_pre <= INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= 25)) (PreH9 : (0 <= z)) (PreH10 : (z < 475)) (PreH11 : (ShirtScanState score_pre place_pre i z )),
  (ShirtSelection score_pre ((((z * 96 ) + 42 ) % ( 475 ) ) + 26 ) )
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (PreH1 : (26 <= p_pre)) (PreH2 : (p_pre <= 500)) (PreH3 : (1 <= y_pre)) (PreH4 : (y_pre <= x_pre)) (PreH5 : (x_pre <= 20000)) (PreH6 : (Pre p_pre x_pre y_pre )) (PreH7 : (0 <= (score - y_pre ))) (PreH8 : ((score - y_pre ) <= 49)) (PreH9 : (AlignmentSearch x_pre y_pre score )),
  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "score" ) )) # Int  |-> score)
|--
  “ (((score - x_pre ) <> (INT_MIN)) \/ (50 <> (-1))) ”
  &&  “ (50 <> 0) ”
.

Definition solver_safety_wit_2 :=
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (PreH1 : (26 <= p_pre)) (PreH2 : (p_pre <= 500)) (PreH3 : (1 <= y_pre)) (PreH4 : (y_pre <= x_pre)) (PreH5 : (x_pre <= 20000)) (PreH6 : (Pre p_pre x_pre y_pre )) (PreH7 : (0 <= (score - y_pre ))) (PreH8 : ((score - y_pre ) <= 49)) (PreH9 : (AlignmentSearch x_pre y_pre score )),
  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "score" ) )) # Int  |-> score)
|--
  “ ((score - x_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (score - x_pre )) ”
.

Definition solver_safety_wit_3 :=
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (PreH1 : (26 <= p_pre)) (PreH2 : (p_pre <= 500)) (PreH3 : (1 <= y_pre)) (PreH4 : (y_pre <= x_pre)) (PreH5 : (x_pre <= 20000)) (PreH6 : (Pre p_pre x_pre y_pre )) (PreH7 : (0 <= (score - y_pre ))) (PreH8 : ((score - y_pre ) <= 49)) (PreH9 : (AlignmentSearch x_pre y_pre score )),
  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "score" ) )) # Int  |-> score)
|--
  “ (50 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 50) ”
.

Definition solver_safety_wit_4 :=
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (PreH1 : (26 <= p_pre)) (PreH2 : (p_pre <= 500)) (PreH3 : (1 <= y_pre)) (PreH4 : (y_pre <= x_pre)) (PreH5 : (x_pre <= 20000)) (PreH6 : (Pre p_pre x_pre y_pre )) (PreH7 : (0 <= (score - y_pre ))) (PreH8 : ((score - y_pre ) <= 49)) (PreH9 : (AlignmentSearch x_pre y_pre score )),
  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "score" ) )) # Int  |-> score)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_5 :=
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (PreH1 : (((score - x_pre ) % ( 50 ) ) <> 0)) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (Pre p_pre x_pre y_pre )) (PreH8 : (0 <= (score - y_pre ))) (PreH9 : ((score - y_pre ) <= 49)) (PreH10 : (AlignmentSearch x_pre y_pre score )),
  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "score" ) )) # Int  |-> score)
|--
  “ ((score + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (score + 1 )) ”
.

Definition solver_safety_wit_6 :=
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 1)) (PreH3 : (ShirtSelection score p_pre )) (PreH4 : (26 <= p_pre)) (PreH5 : (p_pre <= 500)) (PreH6 : (1 <= y_pre)) (PreH7 : (y_pre <= x_pre)) (PreH8 : (x_pre <= 20000)) (PreH9 : (Pre p_pre x_pre y_pre )) (PreH10 : (y_pre <= score)) (PreH11 : (score <= (x_pre + (50 * 475 ) ))) (PreH12 : (CandidateSearch p_pre x_pre y_pre score )),
  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "score" ) )) # Int  |-> score)
|--
  “ False ”
.

Definition solver_safety_wit_7 :=
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 0)) (PreH3 : (NoShirtSelection score p_pre )) (PreH4 : (26 <= p_pre)) (PreH5 : (p_pre <= 500)) (PreH6 : (1 <= y_pre)) (PreH7 : (y_pre <= x_pre)) (PreH8 : (x_pre <= 20000)) (PreH9 : (Pre p_pre x_pre y_pre )) (PreH10 : (y_pre <= score)) (PreH11 : (score <= (x_pre + (50 * 475 ) ))) (PreH12 : (CandidateSearch p_pre x_pre y_pre score )),
  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "score" ) )) # Int  |-> score)
|--
  “ False ”
.

Definition solver_safety_wit_8 :=
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (PreH1 : (26 <= p_pre)) (PreH2 : (p_pre <= 500)) (PreH3 : (1 <= y_pre)) (PreH4 : (y_pre <= x_pre)) (PreH5 : (x_pre <= 20000)) (PreH6 : (Pre p_pre x_pre y_pre )) (PreH7 : (y_pre <= score)) (PreH8 : (score < (x_pre + (50 * 475 ) ))) (PreH9 : (score <= (INT_MAX - 50 ))) (PreH10 : (CandidateSearch p_pre x_pre y_pre score )) (PreH11 : (NoShirtSelection score p_pre )),
  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "score" ) )) # Int  |-> score)
|--
  “ ((score + 50 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (score + 50 )) ”
.

Definition solver_safety_wit_9 :=
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (PreH1 : (26 <= p_pre)) (PreH2 : (p_pre <= 500)) (PreH3 : (1 <= y_pre)) (PreH4 : (y_pre <= x_pre)) (PreH5 : (x_pre <= 20000)) (PreH6 : (Pre p_pre x_pre y_pre )) (PreH7 : (y_pre <= score)) (PreH8 : (score < (x_pre + (50 * 475 ) ))) (PreH9 : (score <= (INT_MAX - 50 ))) (PreH10 : (CandidateSearch p_pre x_pre y_pre score )) (PreH11 : (NoShirtSelection score p_pre )),
  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "score" ) )) # Int  |-> score)
|--
  “ (50 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 50) ”
.

Definition solver_safety_wit_10 :=
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (PreH1 : (score <= x_pre)) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (y_pre <= score)) (PreH8 : (score <= (x_pre + (50 * 475 ) ))) (PreH9 : (FirstWinningCandidate p_pre x_pre y_pre score )),
  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "score" ) )) # Int  |-> score)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_11 :=
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (PreH1 : (score > x_pre)) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (y_pre <= score)) (PreH8 : (score <= (x_pre + (50 * 475 ) ))) (PreH9 : (FirstWinningCandidate p_pre x_pre y_pre score )),
  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "score" ) )) # Int  |-> score)
|--
  “ ((((score - x_pre ) + 99 ) <> (INT_MIN)) \/ (100 <> (-1))) ”
  &&  “ (100 <> 0) ”
.

Definition solver_safety_wit_12 :=
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (PreH1 : (score > x_pre)) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (y_pre <= score)) (PreH8 : (score <= (x_pre + (50 * 475 ) ))) (PreH9 : (FirstWinningCandidate p_pre x_pre y_pre score )),
  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "score" ) )) # Int  |-> score)
|--
  “ (((score - x_pre ) + 99 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((score - x_pre ) + 99 )) ”
.

Definition solver_safety_wit_13 :=
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (PreH1 : (score > x_pre)) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (y_pre <= score)) (PreH8 : (score <= (x_pre + (50 * 475 ) ))) (PreH9 : (FirstWinningCandidate p_pre x_pre y_pre score )),
  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "score" ) )) # Int  |-> score)
|--
  “ ((score - x_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (score - x_pre )) ”
.

Definition solver_safety_wit_14 :=
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (PreH1 : (score > x_pre)) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (y_pre <= score)) (PreH8 : (score <= (x_pre + (50 * 475 ) ))) (PreH9 : (FirstWinningCandidate p_pre x_pre y_pre score )),
  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "score" ) )) # Int  |-> score)
|--
  “ (99 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 99) ”
.

Definition solver_safety_wit_15 :=
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (PreH1 : (score > x_pre)) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (y_pre <= score)) (PreH8 : (score <= (x_pre + (50 * 475 ) ))) (PreH9 : (FirstWinningCandidate p_pre x_pre y_pre score )),
  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "score" ) )) # Int  |-> score)
|--
  “ (100 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 100) ”
.

Definition solver_entail_wit_1 :=
(
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (PreH1 : (26 <= p_pre)) (PreH2 : (p_pre <= 500)) (PreH3 : (1 <= y_pre)) (PreH4 : (y_pre <= x_pre)) (PreH5 : (x_pre <= 20000)) (PreH6 : (Pre p_pre x_pre y_pre )),
  TT && emp 
|--
  “ (26 <= p_pre) ”
  &&  “ (p_pre <= 500) ”
  &&  “ (1 <= y_pre) ”
  &&  “ (y_pre <= x_pre) ”
  &&  “ (x_pre <= 20000) ”
  &&  “ (Pre p_pre x_pre y_pre ) ”
  &&  “ (0 <= (y_pre - y_pre )) ”
  &&  “ ((y_pre - y_pre ) <= 49) ”
  &&  “ (AlignmentSearch x_pre y_pre y_pre ) ”
  &&  emp
) \/
(
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (PreH1 : (26 <= p_pre)) (PreH2 : (p_pre <= 500)) (PreH3 : (1 <= y_pre)) (PreH4 : (y_pre <= x_pre)) (PreH5 : (x_pre <= 20000)) (PreH6 : (Pre p_pre x_pre y_pre )),
  TT && emp 
|--
  “ (AlignmentSearch x_pre y_pre y_pre ) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (PreH1 : (26 <= p_pre)) (PreH2 : (p_pre <= 500)) (PreH3 : (1 <= y_pre)) (PreH4 : (y_pre <= x_pre)) (PreH5 : (x_pre <= 20000)) (PreH6 : (Pre p_pre x_pre y_pre )),
  (AlignmentSearch x_pre y_pre y_pre )
.

Definition solver_entail_wit_2 :=
(
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (PreH1 : (((score - x_pre ) % ( 50 ) ) <> 0)) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (Pre p_pre x_pre y_pre )) (PreH8 : (0 <= (score - y_pre ))) (PreH9 : ((score - y_pre ) <= 49)) (PreH10 : (AlignmentSearch x_pre y_pre score )),
  TT && emp 
|--
  “ (26 <= p_pre) ”
  &&  “ (p_pre <= 500) ”
  &&  “ (1 <= y_pre) ”
  &&  “ (y_pre <= x_pre) ”
  &&  “ (x_pre <= 20000) ”
  &&  “ (Pre p_pre x_pre y_pre ) ”
  &&  “ (0 <= ((score + 1 ) - y_pre )) ”
  &&  “ (((score + 1 ) - y_pre ) <= 49) ”
  &&  “ (AlignmentSearch x_pre y_pre (score + 1 ) ) ”
  &&  emp
) \/
(
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (PreH1 : (((score - x_pre ) % ( 50 ) ) <> 0)) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (Pre p_pre x_pre y_pre )) (PreH8 : (0 <= (score - y_pre ))) (PreH9 : ((score - y_pre ) <= 49)) (PreH10 : (AlignmentSearch x_pre y_pre score )),
  TT && emp 
|--
  “ (AlignmentSearch x_pre y_pre (score + 1 ) ) ”
  &&  “ (((score + 1 ) - y_pre ) <= 49) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 :=
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (PreH1 : (((score - x_pre ) % ( 50 ) ) <> 0)) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (Pre p_pre x_pre y_pre )) (PreH8 : (0 <= (score - y_pre ))) (PreH9 : ((score - y_pre ) <= 49)) (PreH10 : (AlignmentSearch x_pre y_pre score )),
  (AlignmentSearch x_pre y_pre (score + 1 ) )
.

Definition solver_entail_wit_2_split_goal_2 :=
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (PreH1 : (((score - x_pre ) % ( 50 ) ) <> 0)) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (Pre p_pre x_pre y_pre )) (PreH8 : (0 <= (score - y_pre ))) (PreH9 : ((score - y_pre ) <= 49)) (PreH10 : (AlignmentSearch x_pre y_pre score )),
  (((score + 1 ) - y_pre ) <= 49)
.

Definition solver_entail_wit_3 :=
(
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (PreH1 : (((score - x_pre ) % ( 50 ) ) = 0)) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (Pre p_pre x_pre y_pre )) (PreH8 : (0 <= (score - y_pre ))) (PreH9 : ((score - y_pre ) <= 49)) (PreH10 : (AlignmentSearch x_pre y_pre score )),
  TT && emp 
|--
  “ (26 <= p_pre) ”
  &&  “ (p_pre <= 500) ”
  &&  “ (1 <= y_pre) ”
  &&  “ (y_pre <= x_pre) ”
  &&  “ (x_pre <= 20000) ”
  &&  “ (Pre p_pre x_pre y_pre ) ”
  &&  “ (y_pre <= score) ”
  &&  “ (score <= (x_pre + (50 * 475 ) )) ”
  &&  “ (CandidateSearch p_pre x_pre y_pre score ) ”
  &&  emp
) \/
(
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (PreH1 : (((score - x_pre ) % ( 50 ) ) = 0)) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (Pre p_pre x_pre y_pre )) (PreH8 : (0 <= (score - y_pre ))) (PreH9 : ((score - y_pre ) <= 49)) (PreH10 : (AlignmentSearch x_pre y_pre score )),
  TT && emp 
|--
  “ (CandidateSearch p_pre x_pre y_pre score ) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 :=
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (PreH1 : (((score - x_pre ) % ( 50 ) ) = 0)) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (Pre p_pre x_pre y_pre )) (PreH8 : (0 <= (score - y_pre ))) (PreH9 : ((score - y_pre ) <= 49)) (PreH10 : (AlignmentSearch x_pre y_pre score )),
  (CandidateSearch p_pre x_pre y_pre score )
.

Definition solver_entail_wit_4 :=
(
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (NoShirtSelection score p_pre )) (PreH4 : (26 <= p_pre)) (PreH5 : (p_pre <= 500)) (PreH6 : (1 <= y_pre)) (PreH7 : (y_pre <= x_pre)) (PreH8 : (x_pre <= 20000)) (PreH9 : (Pre p_pre x_pre y_pre )) (PreH10 : (y_pre <= score)) (PreH11 : (score <= (x_pre + (50 * 475 ) ))) (PreH12 : (CandidateSearch p_pre x_pre y_pre score )),
  TT && emp 
|--
  “ (26 <= p_pre) ”
  &&  “ (p_pre <= 500) ”
  &&  “ (1 <= y_pre) ”
  &&  “ (y_pre <= x_pre) ”
  &&  “ (x_pre <= 20000) ”
  &&  “ (Pre p_pre x_pre y_pre ) ”
  &&  “ (y_pre <= score) ”
  &&  “ (score < (x_pre + (50 * 475 ) )) ”
  &&  “ (score <= (INT_MAX - 50 )) ”
  &&  “ (CandidateSearch p_pre x_pre y_pre score ) ”
  &&  “ (NoShirtSelection score p_pre ) ”
  &&  emp
) \/
(
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (NoShirtSelection score p_pre )) (PreH4 : (26 <= p_pre)) (PreH5 : (p_pre <= 500)) (PreH6 : (1 <= y_pre)) (PreH7 : (y_pre <= x_pre)) (PreH8 : (x_pre <= 20000)) (PreH9 : (Pre p_pre x_pre y_pre )) (PreH10 : (y_pre <= score)) (PreH11 : (score <= (x_pre + (50 * 475 ) ))) (PreH12 : (CandidateSearch p_pre x_pre y_pre score )),
  TT && emp 
|--
  “ (score < (x_pre + (50 * 475 ) )) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 :=
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (NoShirtSelection score p_pre )) (PreH4 : (26 <= p_pre)) (PreH5 : (p_pre <= 500)) (PreH6 : (1 <= y_pre)) (PreH7 : (y_pre <= x_pre)) (PreH8 : (x_pre <= 20000)) (PreH9 : (Pre p_pre x_pre y_pre )) (PreH10 : (y_pre <= score)) (PreH11 : (score <= (x_pre + (50 * 475 ) ))) (PreH12 : (CandidateSearch p_pre x_pre y_pre score )),
  (score < (x_pre + (50 * 475 ) ))
.

Definition solver_entail_wit_5 :=
(
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (PreH1 : (26 <= p_pre)) (PreH2 : (p_pre <= 500)) (PreH3 : (1 <= y_pre)) (PreH4 : (y_pre <= x_pre)) (PreH5 : (x_pre <= 20000)) (PreH6 : (Pre p_pre x_pre y_pre )) (PreH7 : (y_pre <= score)) (PreH8 : (score < (x_pre + (50 * 475 ) ))) (PreH9 : (score <= (INT_MAX - 50 ))) (PreH10 : (CandidateSearch p_pre x_pre y_pre score )) (PreH11 : (NoShirtSelection score p_pre )),
  TT && emp 
|--
  “ (26 <= p_pre) ”
  &&  “ (p_pre <= 500) ”
  &&  “ (1 <= y_pre) ”
  &&  “ (y_pre <= x_pre) ”
  &&  “ (x_pre <= 20000) ”
  &&  “ (Pre p_pre x_pre y_pre ) ”
  &&  “ (y_pre <= (score + 50 )) ”
  &&  “ ((score + 50 ) <= (x_pre + (50 * 475 ) )) ”
  &&  “ (CandidateSearch p_pre x_pre y_pre (score + 50 ) ) ”
  &&  emp
) \/
(
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (PreH1 : (26 <= p_pre)) (PreH2 : (p_pre <= 500)) (PreH3 : (1 <= y_pre)) (PreH4 : (y_pre <= x_pre)) (PreH5 : (x_pre <= 20000)) (PreH6 : (Pre p_pre x_pre y_pre )) (PreH7 : (y_pre <= score)) (PreH8 : (score < (x_pre + (50 * 475 ) ))) (PreH9 : (score <= (INT_MAX - 50 ))) (PreH10 : (CandidateSearch p_pre x_pre y_pre score )) (PreH11 : (NoShirtSelection score p_pre )),
  TT && emp 
|--
  “ (CandidateSearch p_pre x_pre y_pre (score + 50 ) ) ”
  &&  “ ((score + 50 ) <= (x_pre + (50 * 475 ) )) ”
  &&  emp
).

Definition solver_entail_wit_5_split_goal_1 :=
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (PreH1 : (26 <= p_pre)) (PreH2 : (p_pre <= 500)) (PreH3 : (1 <= y_pre)) (PreH4 : (y_pre <= x_pre)) (PreH5 : (x_pre <= 20000)) (PreH6 : (Pre p_pre x_pre y_pre )) (PreH7 : (y_pre <= score)) (PreH8 : (score < (x_pre + (50 * 475 ) ))) (PreH9 : (score <= (INT_MAX - 50 ))) (PreH10 : (CandidateSearch p_pre x_pre y_pre score )) (PreH11 : (NoShirtSelection score p_pre )),
  (CandidateSearch p_pre x_pre y_pre (score + 50 ) )
.

Definition solver_entail_wit_5_split_goal_2 :=
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (PreH1 : (26 <= p_pre)) (PreH2 : (p_pre <= 500)) (PreH3 : (1 <= y_pre)) (PreH4 : (y_pre <= x_pre)) (PreH5 : (x_pre <= 20000)) (PreH6 : (Pre p_pre x_pre y_pre )) (PreH7 : (y_pre <= score)) (PreH8 : (score < (x_pre + (50 * 475 ) ))) (PreH9 : (score <= (INT_MAX - 50 ))) (PreH10 : (CandidateSearch p_pre x_pre y_pre score )) (PreH11 : (NoShirtSelection score p_pre )),
  ((score + 50 ) <= (x_pre + (50 * 475 ) ))
.

Definition solver_entail_wit_6 :=
(
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 1)) (PreH3 : (ShirtSelection score p_pre )) (PreH4 : (26 <= p_pre)) (PreH5 : (p_pre <= 500)) (PreH6 : (1 <= y_pre)) (PreH7 : (y_pre <= x_pre)) (PreH8 : (x_pre <= 20000)) (PreH9 : (Pre p_pre x_pre y_pre )) (PreH10 : (y_pre <= score)) (PreH11 : (score <= (x_pre + (50 * 475 ) ))) (PreH12 : (CandidateSearch p_pre x_pre y_pre score )),
  TT && emp 
|--
  “ (26 <= p_pre) ”
  &&  “ (p_pre <= 500) ”
  &&  “ (1 <= y_pre) ”
  &&  “ (y_pre <= x_pre) ”
  &&  “ (x_pre <= 20000) ”
  &&  “ (y_pre <= score) ”
  &&  “ (score <= (x_pre + (50 * 475 ) )) ”
  &&  “ (FirstWinningCandidate p_pre x_pre y_pre score ) ”
  &&  emp
) \/
(
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 1)) (PreH3 : (ShirtSelection score p_pre )) (PreH4 : (26 <= p_pre)) (PreH5 : (p_pre <= 500)) (PreH6 : (1 <= y_pre)) (PreH7 : (y_pre <= x_pre)) (PreH8 : (x_pre <= 20000)) (PreH9 : (Pre p_pre x_pre y_pre )) (PreH10 : (y_pre <= score)) (PreH11 : (score <= (x_pre + (50 * 475 ) ))) (PreH12 : (CandidateSearch p_pre x_pre y_pre score )),
  TT && emp 
|--
  “ (FirstWinningCandidate p_pre x_pre y_pre score ) ”
  &&  emp
).

Definition solver_entail_wit_6_split_goal_1 :=
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 1)) (PreH3 : (ShirtSelection score p_pre )) (PreH4 : (26 <= p_pre)) (PreH5 : (p_pre <= 500)) (PreH6 : (1 <= y_pre)) (PreH7 : (y_pre <= x_pre)) (PreH8 : (x_pre <= 20000)) (PreH9 : (Pre p_pre x_pre y_pre )) (PreH10 : (y_pre <= score)) (PreH11 : (score <= (x_pre + (50 * 475 ) ))) (PreH12 : (CandidateSearch p_pre x_pre y_pre score )),
  (FirstWinningCandidate p_pre x_pre y_pre score )
.

Definition solver_return_wit_1 :=
(
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (PreH1 : (score <= x_pre)) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (y_pre <= score)) (PreH8 : (score <= (x_pre + (50 * 475 ) ))) (PreH9 : (FirstWinningCandidate p_pre x_pre y_pre score )),
  TT && emp 
|--
  “ (Spec p_pre x_pre y_pre 0 ) ”
  &&  emp
) \/
(
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (PreH1 : (score <= x_pre)) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (y_pre <= score)) (PreH8 : (score <= (x_pre + (50 * 475 ) ))) (PreH9 : (FirstWinningCandidate p_pre x_pre y_pre score )),
  TT && emp 
|--
  “ (Spec p_pre x_pre y_pre 0 ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (PreH1 : (score <= x_pre)) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (y_pre <= score)) (PreH8 : (score <= (x_pre + (50 * 475 ) ))) (PreH9 : (FirstWinningCandidate p_pre x_pre y_pre score )),
  (Spec p_pre x_pre y_pre 0 )
.

Definition solver_return_wit_2 :=
(
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (PreH1 : (score > x_pre)) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (y_pre <= score)) (PreH8 : (score <= (x_pre + (50 * 475 ) ))) (PreH9 : (FirstWinningCandidate p_pre x_pre y_pre score )),
  TT && emp 
|--
  “ (Spec p_pre x_pre y_pre (((score - x_pre ) + 99 ) ÷ 100 ) ) ”
  &&  emp
) \/
(
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (PreH1 : (score > x_pre)) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (y_pre <= score)) (PreH8 : (score <= (x_pre + (50 * 475 ) ))) (PreH9 : (FirstWinningCandidate p_pre x_pre y_pre score )),
  TT && emp 
|--
  “ (Spec p_pre x_pre y_pre (((score - x_pre ) + 99 ) ÷ 100 ) ) ”
  &&  emp
).

Definition solver_return_wit_2_split_goal_1 :=
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (PreH1 : (score > x_pre)) (PreH2 : (26 <= p_pre)) (PreH3 : (p_pre <= 500)) (PreH4 : (1 <= y_pre)) (PreH5 : (y_pre <= x_pre)) (PreH6 : (x_pre <= 20000)) (PreH7 : (y_pre <= score)) (PreH8 : (score <= (x_pre + (50 * 475 ) ))) (PreH9 : (FirstWinningCandidate p_pre x_pre y_pre score )),
  (Spec p_pre x_pre y_pre (((score - x_pre ) + 99 ) ÷ 100 ) )
.

Definition solver_partial_solve_wit_1_pure :=
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (PreH1 : (26 <= p_pre)) (PreH2 : (p_pre <= 500)) (PreH3 : (1 <= y_pre)) (PreH4 : (y_pre <= x_pre)) (PreH5 : (x_pre <= 20000)) (PreH6 : (Pre p_pre x_pre y_pre )) (PreH7 : (y_pre <= score)) (PreH8 : (score <= (x_pre + (50 * 475 ) ))) (PreH9 : (CandidateSearch p_pre x_pre y_pre score )),
  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "score" ) )) # Int  |-> score)
|--
  “ (26 <= p_pre) ”
  &&  “ (p_pre <= 500) ”
  &&  “ (0 <= score) ”
  &&  “ (score <= INT_MAX) ”
.

Definition solver_partial_solve_wit_1_aux :=
forall (p_pre: Z) (x_pre: Z) (y_pre: Z) (score: Z) (PreH1 : (26 <= p_pre)) (PreH2 : (p_pre <= 500)) (PreH3 : (1 <= y_pre)) (PreH4 : (y_pre <= x_pre)) (PreH5 : (x_pre <= 20000)) (PreH6 : (Pre p_pre x_pre y_pre )) (PreH7 : (y_pre <= score)) (PreH8 : (score <= (x_pre + (50 * 475 ) ))) (PreH9 : (CandidateSearch p_pre x_pre y_pre score )),
  TT && emp 
|--
  “ (26 <= p_pre) ”
  &&  “ (p_pre <= 500) ”
  &&  “ (0 <= score) ”
  &&  “ (score <= INT_MAX) ”
  &&  “ (26 <= p_pre) ”
  &&  “ (p_pre <= 500) ”
  &&  “ (1 <= y_pre) ”
  &&  “ (y_pre <= x_pre) ”
  &&  “ (x_pre <= 20000) ”
  &&  “ (Pre p_pre x_pre y_pre ) ”
  &&  “ (y_pre <= score) ”
  &&  “ (score <= (x_pre + (50 * 475 ) )) ”
  &&  “ (CandidateSearch p_pre x_pre y_pre score ) ”
  &&  emp
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Module Type VC_Correct.


Axiom proof_of_wins_safety_wit_1 : wins_safety_wit_1.
Axiom proof_of_wins_safety_wit_2 : wins_safety_wit_2.
Axiom proof_of_wins_safety_wit_3 : wins_safety_wit_3.
Axiom proof_of_wins_safety_wit_4 : wins_safety_wit_4.
Axiom proof_of_wins_safety_wit_5 : wins_safety_wit_5.
Axiom proof_of_wins_safety_wit_6 : wins_safety_wit_6.
Axiom proof_of_wins_safety_wit_7 : wins_safety_wit_7.
Axiom proof_of_wins_safety_wit_8 : wins_safety_wit_8.
Axiom proof_of_wins_safety_wit_9 : wins_safety_wit_9.
Axiom proof_of_wins_safety_wit_10 : wins_safety_wit_10.
Axiom proof_of_wins_safety_wit_11 : wins_safety_wit_11.
Axiom proof_of_wins_safety_wit_12 : wins_safety_wit_12.
Axiom proof_of_wins_safety_wit_13 : wins_safety_wit_13.
Axiom proof_of_wins_safety_wit_14 : wins_safety_wit_14.
Axiom proof_of_wins_safety_wit_15 : wins_safety_wit_15.
Axiom proof_of_wins_safety_wit_16 : wins_safety_wit_16.
Axiom proof_of_wins_safety_wit_17 : wins_safety_wit_17.
Axiom proof_of_wins_entail_wit_1 : wins_entail_wit_1.
Axiom proof_of_wins_entail_wit_2 : wins_entail_wit_2.
Axiom proof_of_wins_return_wit_1 : wins_return_wit_1.
Axiom proof_of_wins_return_wit_2 : wins_return_wit_2.
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.

End VC_Correct.
