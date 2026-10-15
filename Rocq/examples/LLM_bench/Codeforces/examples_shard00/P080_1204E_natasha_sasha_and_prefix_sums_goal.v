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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P080_1204E_natasha_sasha_and_prefix_sums_lib.
Local Open Scope sac.

(*----- Function modpow -----*)

Definition modpow_safety_wit_1 := 
forall (e_pre: Z) (a_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre < 998244853)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) ,
  ((( &( "r" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "e" ) )) # Int64  |-> e_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition modpow_safety_wit_2 := 
forall (e_pre: Z) (a_pre: Z) (r: Z) (a: Z) (e: Z) (PreH1 : (0 <= e)) (PreH2 : (e <= e_pre)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) (PreH5 : (0 <= a)) (PreH6 : (a < 998244853)) (PreH7 : (0 <= r)) (PreH8 : (r < 998244853)) (PreH9 : (((r * (Z.pow (a) (e)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))) (PreH10 : (e <> 0)) ,
  ((( &( "e" ) )) # Int64  |-> e)
  **  ((( &( "a" ) )) # Int64  |-> a)
  **  ((( &( "r" ) )) # Int64  |-> r)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition modpow_safety_wit_3 := 
forall (e_pre: Z) (a_pre: Z) (r: Z) (a: Z) (e: Z) (PreH1 : (0 <= e)) (PreH2 : (e <= e_pre)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) (PreH5 : (0 <= a)) (PreH6 : (a < 998244853)) (PreH7 : (0 <= r)) (PreH8 : (r < 998244853)) (PreH9 : (((r * (Z.pow (a) (e)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))) (PreH10 : (e <> 0)) (PreH11 : ((Z.land e 1) <> 0)) ,
  ((( &( "e" ) )) # Int64  |-> e)
  **  ((( &( "a" ) )) # Int64  |-> a)
  **  ((( &( "r" ) )) # Int64  |-> r)
|--
  “ (((r * a ) <> (INT64_MIN)) \/ (998244853 <> (-1))) ” 
  &&  “ (998244853 <> 0) ”
.

Definition modpow_safety_wit_4 := 
forall (e_pre: Z) (a_pre: Z) (r: Z) (a: Z) (e: Z) (PreH1 : (0 <= e)) (PreH2 : (e <= e_pre)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) (PreH5 : (0 <= a)) (PreH6 : (a < 998244853)) (PreH7 : (0 <= r)) (PreH8 : (r < 998244853)) (PreH9 : (((r * (Z.pow (a) (e)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))) (PreH10 : (e <> 0)) (PreH11 : ((Z.land e 1) <> 0)) ,
  ((( &( "e" ) )) # Int64  |-> e)
  **  ((( &( "a" ) )) # Int64  |-> a)
  **  ((( &( "r" ) )) # Int64  |-> r)
|--
  “ ((r * a ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (r * a )) ”
.

Definition modpow_safety_wit_5 := 
forall (e_pre: Z) (a_pre: Z) (r: Z) (a: Z) (e: Z) (PreH1 : (0 <= e)) (PreH2 : (e <= e_pre)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) (PreH5 : (0 <= a)) (PreH6 : (a < 998244853)) (PreH7 : (0 <= r)) (PreH8 : (r < 998244853)) (PreH9 : (((r * (Z.pow (a) (e)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))) (PreH10 : (e <> 0)) (PreH11 : ((Z.land e 1) <> 0)) ,
  ((( &( "e" ) )) # Int64  |-> e)
  **  ((( &( "a" ) )) # Int64  |-> a)
  **  ((( &( "r" ) )) # Int64  |-> r)
|--
  “ (998244853 <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= 998244853) ”
.

Definition modpow_safety_wit_6 := 
forall (e_pre: Z) (a_pre: Z) (r: Z) (a: Z) (e: Z) (PreH1 : (0 <= e)) (PreH2 : (e <= e_pre)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) (PreH5 : (0 <= a)) (PreH6 : (a < 998244853)) (PreH7 : (0 <= r)) (PreH8 : (r < 998244853)) (PreH9 : (((r * (Z.pow (a) (e)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))) (PreH10 : (e <> 0)) (PreH11 : ((Z.land e 1) <> 0)) ,
  ((( &( "e" ) )) # Int64  |-> e)
  **  ((( &( "a" ) )) # Int64  |-> a)
  **  ((( &( "r" ) )) # Int64  |-> ((r * a ) % ( 998244853 ) ))
|--
  “ (((a * a ) <> (INT64_MIN)) \/ (998244853 <> (-1))) ” 
  &&  “ (998244853 <> 0) ”
.

Definition modpow_safety_wit_7 := 
forall (e_pre: Z) (a_pre: Z) (r: Z) (a: Z) (e: Z) (PreH1 : (0 <= e)) (PreH2 : (e <= e_pre)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) (PreH5 : (0 <= a)) (PreH6 : (a < 998244853)) (PreH7 : (0 <= r)) (PreH8 : (r < 998244853)) (PreH9 : (((r * (Z.pow (a) (e)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))) (PreH10 : (e <> 0)) (PreH11 : ((Z.land e 1) <> 0)) ,
  ((( &( "e" ) )) # Int64  |-> e)
  **  ((( &( "a" ) )) # Int64  |-> a)
  **  ((( &( "r" ) )) # Int64  |-> ((r * a ) % ( 998244853 ) ))
|--
  “ ((a * a ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (a * a )) ”
.

Definition modpow_safety_wit_8 := 
forall (e_pre: Z) (a_pre: Z) (r: Z) (a: Z) (e: Z) (PreH1 : (0 <= e)) (PreH2 : (e <= e_pre)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) (PreH5 : (0 <= a)) (PreH6 : (a < 998244853)) (PreH7 : (0 <= r)) (PreH8 : (r < 998244853)) (PreH9 : (((r * (Z.pow (a) (e)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))) (PreH10 : (e <> 0)) (PreH11 : ((Z.land e 1) <> 0)) ,
  ((( &( "e" ) )) # Int64  |-> e)
  **  ((( &( "a" ) )) # Int64  |-> a)
  **  ((( &( "r" ) )) # Int64  |-> ((r * a ) % ( 998244853 ) ))
|--
  “ (998244853 <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= 998244853) ”
.

Definition modpow_safety_wit_9 := 
forall (e_pre: Z) (a_pre: Z) (r: Z) (a: Z) (e: Z) (PreH1 : (0 <= e)) (PreH2 : (e <= e_pre)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) (PreH5 : (0 <= a)) (PreH6 : (a < 998244853)) (PreH7 : (0 <= r)) (PreH8 : (r < 998244853)) (PreH9 : (((r * (Z.pow (a) (e)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))) (PreH10 : (e <> 0)) (PreH11 : ((Z.land e 1) = 0)) ,
  ((( &( "e" ) )) # Int64  |-> e)
  **  ((( &( "a" ) )) # Int64  |-> a)
  **  ((( &( "r" ) )) # Int64  |-> r)
|--
  “ (((a * a ) <> (INT64_MIN)) \/ (998244853 <> (-1))) ” 
  &&  “ (998244853 <> 0) ”
.

Definition modpow_safety_wit_10 := 
forall (e_pre: Z) (a_pre: Z) (r: Z) (a: Z) (e: Z) (PreH1 : (0 <= e)) (PreH2 : (e <= e_pre)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) (PreH5 : (0 <= a)) (PreH6 : (a < 998244853)) (PreH7 : (0 <= r)) (PreH8 : (r < 998244853)) (PreH9 : (((r * (Z.pow (a) (e)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))) (PreH10 : (e <> 0)) (PreH11 : ((Z.land e 1) = 0)) ,
  ((( &( "e" ) )) # Int64  |-> e)
  **  ((( &( "a" ) )) # Int64  |-> a)
  **  ((( &( "r" ) )) # Int64  |-> r)
|--
  “ ((a * a ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (a * a )) ”
.

Definition modpow_safety_wit_11 := 
forall (e_pre: Z) (a_pre: Z) (r: Z) (a: Z) (e: Z) (PreH1 : (0 <= e)) (PreH2 : (e <= e_pre)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) (PreH5 : (0 <= a)) (PreH6 : (a < 998244853)) (PreH7 : (0 <= r)) (PreH8 : (r < 998244853)) (PreH9 : (((r * (Z.pow (a) (e)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))) (PreH10 : (e <> 0)) (PreH11 : ((Z.land e 1) = 0)) ,
  ((( &( "e" ) )) # Int64  |-> e)
  **  ((( &( "a" ) )) # Int64  |-> a)
  **  ((( &( "r" ) )) # Int64  |-> r)
|--
  “ (998244853 <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= 998244853) ”
.

Definition modpow_safety_wit_12 := 
forall (e_pre: Z) (a_pre: Z) (r: Z) (a: Z) (e: Z) (PreH1 : (0 <= e)) (PreH2 : (e <= e_pre)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) (PreH5 : (0 <= a)) (PreH6 : (a < 998244853)) (PreH7 : (0 <= r)) (PreH8 : (r < 998244853)) (PreH9 : (((r * (Z.pow (a) (e)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))) (PreH10 : (e <> 0)) (PreH11 : ((Z.land e 1) <> 0)) ,
  ((( &( "e" ) )) # Int64  |-> e)
  **  ((( &( "a" ) )) # Int64  |-> ((a * a ) % ( 998244853 ) ))
  **  ((( &( "r" ) )) # Int64  |-> ((r * a ) % ( 998244853 ) ))
|--
  “ (0 <= e) ” 
  &&  “ (1 <= 63) ” 
  &&  “ (0 <= 1) ”
.

Definition modpow_safety_wit_13 := 
forall (e_pre: Z) (a_pre: Z) (r: Z) (a: Z) (e: Z) (PreH1 : (0 <= e)) (PreH2 : (e <= e_pre)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) (PreH5 : (0 <= a)) (PreH6 : (a < 998244853)) (PreH7 : (0 <= r)) (PreH8 : (r < 998244853)) (PreH9 : (((r * (Z.pow (a) (e)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))) (PreH10 : (e <> 0)) (PreH11 : ((Z.land e 1) <> 0)) ,
  ((( &( "e" ) )) # Int64  |-> e)
  **  ((( &( "a" ) )) # Int64  |-> ((a * a ) % ( 998244853 ) ))
  **  ((( &( "r" ) )) # Int64  |-> ((r * a ) % ( 998244853 ) ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition modpow_safety_wit_14 := 
forall (e_pre: Z) (a_pre: Z) (r: Z) (a: Z) (e: Z) (PreH1 : (0 <= e)) (PreH2 : (e <= e_pre)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) (PreH5 : (0 <= a)) (PreH6 : (a < 998244853)) (PreH7 : (0 <= r)) (PreH8 : (r < 998244853)) (PreH9 : (((r * (Z.pow (a) (e)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))) (PreH10 : (e <> 0)) (PreH11 : ((Z.land e 1) = 0)) ,
  ((( &( "e" ) )) # Int64  |-> e)
  **  ((( &( "a" ) )) # Int64  |-> ((a * a ) % ( 998244853 ) ))
  **  ((( &( "r" ) )) # Int64  |-> r)
|--
  “ (0 <= e) ” 
  &&  “ (1 <= 63) ” 
  &&  “ (0 <= 1) ”
.

Definition modpow_safety_wit_15 := 
forall (e_pre: Z) (a_pre: Z) (r: Z) (a: Z) (e: Z) (PreH1 : (0 <= e)) (PreH2 : (e <= e_pre)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) (PreH5 : (0 <= a)) (PreH6 : (a < 998244853)) (PreH7 : (0 <= r)) (PreH8 : (r < 998244853)) (PreH9 : (((r * (Z.pow (a) (e)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))) (PreH10 : (e <> 0)) (PreH11 : ((Z.land e 1) = 0)) ,
  ((( &( "e" ) )) # Int64  |-> e)
  **  ((( &( "a" ) )) # Int64  |-> ((a * a ) % ( 998244853 ) ))
  **  ((( &( "r" ) )) # Int64  |-> r)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition modpow_entail_wit_1 := 
(
forall (e_pre: Z) (a_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre < 998244853)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) ,
  TT && emp 
|--
  “ (0 <= e_pre) ” 
  &&  “ (e_pre <= e_pre) ” 
  &&  “ (0 <= e_pre) ” 
  &&  “ (e_pre <= 998244853) ” 
  &&  “ (0 <= a_pre) ” 
  &&  “ (a_pre < 998244853) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 < 998244853) ” 
  &&  “ (((1 * (Z.pow (a_pre) (e_pre)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) )) ”
  &&  emp
) \/
(
forall (e_pre: Z) (a_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre < 998244853)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) ,
  TT && emp 
|--
  “ (((1 * (Z.pow (a_pre) (e_pre)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) )) ”
  &&  emp
).

Definition modpow_entail_wit_1_split_goal_1 := 
forall (e_pre: Z) (a_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre < 998244853)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) ,
  (((1 * (Z.pow (a_pre) (e_pre)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))
.

Definition modpow_entail_wit_2_1 := 
(
forall (e_pre: Z) (a_pre: Z) (r: Z) (a: Z) (e: Z) (PreH1 : (0 <= e)) (PreH2 : (e <= e_pre)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) (PreH5 : (0 <= a)) (PreH6 : (a < 998244853)) (PreH7 : (0 <= r)) (PreH8 : (r < 998244853)) (PreH9 : (((r * (Z.pow (a) (e)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))) (PreH10 : (e <> 0)) (PreH11 : ((Z.land e 1) <> 0)) ,
  TT && emp 
|--
  “ (0 <= (Z.shiftr e 1)) ” 
  &&  “ ((Z.shiftr e 1) <= e_pre) ” 
  &&  “ (0 <= e_pre) ” 
  &&  “ (e_pre <= 998244853) ” 
  &&  “ (0 <= ((a * a ) % ( 998244853 ) )) ” 
  &&  “ (((a * a ) % ( 998244853 ) ) < 998244853) ” 
  &&  “ (0 <= ((r * a ) % ( 998244853 ) )) ” 
  &&  “ (((r * a ) % ( 998244853 ) ) < 998244853) ” 
  &&  “ (((((r * a ) % ( 998244853 ) ) * (Z.pow (((a * a ) % ( 998244853 ) )) ((Z.shiftr e 1))) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) )) ”
  &&  emp
) \/
(
forall (e_pre: Z) (a_pre: Z) (r: Z) (a: Z) (e: Z) (PreH1 : (0 <= e)) (PreH2 : (e <= e_pre)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) (PreH5 : (0 <= a)) (PreH6 : (a < 998244853)) (PreH7 : (0 <= r)) (PreH8 : (r < 998244853)) (PreH9 : (((r * (Z.pow (a) (e)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))) (PreH10 : (e <> 0)) (PreH11 : ((Z.land e 1) <> 0)) ,
  TT && emp 
|--
  “ (((((r * a ) % ( 998244853 ) ) * (Z.pow (((a * a ) % ( 998244853 ) )) ((Z.shiftr e 1))) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) )) ” 
  &&  “ (((r * a ) % ( 998244853 ) ) < 998244853) ” 
  &&  “ (0 <= ((r * a ) % ( 998244853 ) )) ” 
  &&  “ (((a * a ) % ( 998244853 ) ) < 998244853) ” 
  &&  “ (0 <= ((a * a ) % ( 998244853 ) )) ” 
  &&  “ ((Z.shiftr e 1) <= e_pre) ” 
  &&  “ (0 <= (Z.shiftr e 1)) ”
  &&  emp
).

Definition modpow_entail_wit_2_1_split_goal_1 := 
forall (e_pre: Z) (a_pre: Z) (r: Z) (a: Z) (e: Z) (PreH1 : (0 <= e)) (PreH2 : (e <= e_pre)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) (PreH5 : (0 <= a)) (PreH6 : (a < 998244853)) (PreH7 : (0 <= r)) (PreH8 : (r < 998244853)) (PreH9 : (((r * (Z.pow (a) (e)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))) (PreH10 : (e <> 0)) (PreH11 : ((Z.land e 1) <> 0)) ,
  (((((r * a ) % ( 998244853 ) ) * (Z.pow (((a * a ) % ( 998244853 ) )) ((Z.shiftr e 1))) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))
.

Definition modpow_entail_wit_2_1_split_goal_2 := 
forall (e_pre: Z) (a_pre: Z) (r: Z) (a: Z) (e: Z) (PreH1 : (0 <= e)) (PreH2 : (e <= e_pre)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) (PreH5 : (0 <= a)) (PreH6 : (a < 998244853)) (PreH7 : (0 <= r)) (PreH8 : (r < 998244853)) (PreH9 : (((r * (Z.pow (a) (e)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))) (PreH10 : (e <> 0)) (PreH11 : ((Z.land e 1) <> 0)) ,
  (((r * a ) % ( 998244853 ) ) < 998244853)
.

Definition modpow_entail_wit_2_1_split_goal_3 := 
forall (e_pre: Z) (a_pre: Z) (r: Z) (a: Z) (e: Z) (PreH1 : (0 <= e)) (PreH2 : (e <= e_pre)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) (PreH5 : (0 <= a)) (PreH6 : (a < 998244853)) (PreH7 : (0 <= r)) (PreH8 : (r < 998244853)) (PreH9 : (((r * (Z.pow (a) (e)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))) (PreH10 : (e <> 0)) (PreH11 : ((Z.land e 1) <> 0)) ,
  (0 <= ((r * a ) % ( 998244853 ) ))
.

Definition modpow_entail_wit_2_1_split_goal_4 := 
forall (e_pre: Z) (a_pre: Z) (r: Z) (a: Z) (e: Z) (PreH1 : (0 <= e)) (PreH2 : (e <= e_pre)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) (PreH5 : (0 <= a)) (PreH6 : (a < 998244853)) (PreH7 : (0 <= r)) (PreH8 : (r < 998244853)) (PreH9 : (((r * (Z.pow (a) (e)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))) (PreH10 : (e <> 0)) (PreH11 : ((Z.land e 1) <> 0)) ,
  (((a * a ) % ( 998244853 ) ) < 998244853)
.

Definition modpow_entail_wit_2_1_split_goal_5 := 
forall (e_pre: Z) (a_pre: Z) (r: Z) (a: Z) (e: Z) (PreH1 : (0 <= e)) (PreH2 : (e <= e_pre)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) (PreH5 : (0 <= a)) (PreH6 : (a < 998244853)) (PreH7 : (0 <= r)) (PreH8 : (r < 998244853)) (PreH9 : (((r * (Z.pow (a) (e)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))) (PreH10 : (e <> 0)) (PreH11 : ((Z.land e 1) <> 0)) ,
  (0 <= ((a * a ) % ( 998244853 ) ))
.

Definition modpow_entail_wit_2_1_split_goal_6 := 
forall (e_pre: Z) (a_pre: Z) (r: Z) (a: Z) (e: Z) (PreH1 : (0 <= e)) (PreH2 : (e <= e_pre)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) (PreH5 : (0 <= a)) (PreH6 : (a < 998244853)) (PreH7 : (0 <= r)) (PreH8 : (r < 998244853)) (PreH9 : (((r * (Z.pow (a) (e)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))) (PreH10 : (e <> 0)) (PreH11 : ((Z.land e 1) <> 0)) ,
  ((Z.shiftr e 1) <= e_pre)
.

Definition modpow_entail_wit_2_1_split_goal_7 := 
forall (e_pre: Z) (a_pre: Z) (r: Z) (a: Z) (e: Z) (PreH1 : (0 <= e)) (PreH2 : (e <= e_pre)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) (PreH5 : (0 <= a)) (PreH6 : (a < 998244853)) (PreH7 : (0 <= r)) (PreH8 : (r < 998244853)) (PreH9 : (((r * (Z.pow (a) (e)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))) (PreH10 : (e <> 0)) (PreH11 : ((Z.land e 1) <> 0)) ,
  (0 <= (Z.shiftr e 1))
.

Definition modpow_entail_wit_2_2 := 
(
forall (e_pre: Z) (a_pre: Z) (r: Z) (a: Z) (e: Z) (PreH1 : (0 <= e)) (PreH2 : (e <= e_pre)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) (PreH5 : (0 <= a)) (PreH6 : (a < 998244853)) (PreH7 : (0 <= r)) (PreH8 : (r < 998244853)) (PreH9 : (((r * (Z.pow (a) (e)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))) (PreH10 : (e <> 0)) (PreH11 : ((Z.land e 1) = 0)) ,
  TT && emp 
|--
  “ (0 <= (Z.shiftr e 1)) ” 
  &&  “ ((Z.shiftr e 1) <= e_pre) ” 
  &&  “ (0 <= e_pre) ” 
  &&  “ (e_pre <= 998244853) ” 
  &&  “ (0 <= ((a * a ) % ( 998244853 ) )) ” 
  &&  “ (((a * a ) % ( 998244853 ) ) < 998244853) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < 998244853) ” 
  &&  “ (((r * (Z.pow (((a * a ) % ( 998244853 ) )) ((Z.shiftr e 1))) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) )) ”
  &&  emp
) \/
(
forall (e_pre: Z) (a_pre: Z) (r: Z) (a: Z) (e: Z) (PreH1 : (0 <= e)) (PreH2 : (e <= e_pre)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) (PreH5 : (0 <= a)) (PreH6 : (a < 998244853)) (PreH7 : (0 <= r)) (PreH8 : (r < 998244853)) (PreH9 : (((r * (Z.pow (a) (e)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))) (PreH10 : (e <> 0)) (PreH11 : ((Z.land e 1) = 0)) ,
  TT && emp 
|--
  “ (((r * (Z.pow (((a * a ) % ( 998244853 ) )) ((Z.shiftr e 1))) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) )) ” 
  &&  “ (((a * a ) % ( 998244853 ) ) < 998244853) ” 
  &&  “ (0 <= ((a * a ) % ( 998244853 ) )) ” 
  &&  “ ((Z.shiftr e 1) <= e_pre) ” 
  &&  “ (0 <= (Z.shiftr e 1)) ”
  &&  emp
).

Definition modpow_entail_wit_2_2_split_goal_1 := 
forall (e_pre: Z) (a_pre: Z) (r: Z) (a: Z) (e: Z) (PreH1 : (0 <= e)) (PreH2 : (e <= e_pre)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) (PreH5 : (0 <= a)) (PreH6 : (a < 998244853)) (PreH7 : (0 <= r)) (PreH8 : (r < 998244853)) (PreH9 : (((r * (Z.pow (a) (e)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))) (PreH10 : (e <> 0)) (PreH11 : ((Z.land e 1) = 0)) ,
  (((r * (Z.pow (((a * a ) % ( 998244853 ) )) ((Z.shiftr e 1))) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))
.

Definition modpow_entail_wit_2_2_split_goal_2 := 
forall (e_pre: Z) (a_pre: Z) (r: Z) (a: Z) (e: Z) (PreH1 : (0 <= e)) (PreH2 : (e <= e_pre)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) (PreH5 : (0 <= a)) (PreH6 : (a < 998244853)) (PreH7 : (0 <= r)) (PreH8 : (r < 998244853)) (PreH9 : (((r * (Z.pow (a) (e)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))) (PreH10 : (e <> 0)) (PreH11 : ((Z.land e 1) = 0)) ,
  (((a * a ) % ( 998244853 ) ) < 998244853)
.

Definition modpow_entail_wit_2_2_split_goal_3 := 
forall (e_pre: Z) (a_pre: Z) (r: Z) (a: Z) (e: Z) (PreH1 : (0 <= e)) (PreH2 : (e <= e_pre)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) (PreH5 : (0 <= a)) (PreH6 : (a < 998244853)) (PreH7 : (0 <= r)) (PreH8 : (r < 998244853)) (PreH9 : (((r * (Z.pow (a) (e)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))) (PreH10 : (e <> 0)) (PreH11 : ((Z.land e 1) = 0)) ,
  (0 <= ((a * a ) % ( 998244853 ) ))
.

Definition modpow_entail_wit_2_2_split_goal_4 := 
forall (e_pre: Z) (a_pre: Z) (r: Z) (a: Z) (e: Z) (PreH1 : (0 <= e)) (PreH2 : (e <= e_pre)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) (PreH5 : (0 <= a)) (PreH6 : (a < 998244853)) (PreH7 : (0 <= r)) (PreH8 : (r < 998244853)) (PreH9 : (((r * (Z.pow (a) (e)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))) (PreH10 : (e <> 0)) (PreH11 : ((Z.land e 1) = 0)) ,
  ((Z.shiftr e 1) <= e_pre)
.

Definition modpow_entail_wit_2_2_split_goal_5 := 
forall (e_pre: Z) (a_pre: Z) (r: Z) (a: Z) (e: Z) (PreH1 : (0 <= e)) (PreH2 : (e <= e_pre)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) (PreH5 : (0 <= a)) (PreH6 : (a < 998244853)) (PreH7 : (0 <= r)) (PreH8 : (r < 998244853)) (PreH9 : (((r * (Z.pow (a) (e)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))) (PreH10 : (e <> 0)) (PreH11 : ((Z.land e 1) = 0)) ,
  (0 <= (Z.shiftr e 1))
.

Definition modpow_return_wit_1 := 
(
forall (e_pre: Z) (a_pre: Z) (r: Z) (a: Z) (e: Z) (PreH1 : (0 <= e)) (PreH2 : (e <= e_pre)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) (PreH5 : (0 <= a)) (PreH6 : (a < 998244853)) (PreH7 : (0 <= r)) (PreH8 : (r < 998244853)) (PreH9 : (((r * (Z.pow (a) (e)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))) (PreH10 : (e = 0)) ,
  TT && emp 
|--
  “ (r = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) )) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < 998244853) ”
  &&  emp
) \/
(
forall (e_pre: Z) (a_pre: Z) (r: Z) (a: Z) (e: Z) (PreH1 : (0 <= e)) (PreH2 : (e <= e_pre)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) (PreH5 : (0 <= a)) (PreH6 : (a < 998244853)) (PreH7 : (0 <= r)) (PreH8 : (r < 998244853)) (PreH9 : (((r * (Z.pow (a) (e)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))) (PreH10 : (e = 0)) ,
  TT && emp 
|--
  “ (r = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) )) ”
  &&  emp
).

Definition modpow_return_wit_1_split_goal_1 := 
forall (e_pre: Z) (a_pre: Z) (r: Z) (a: Z) (e: Z) (PreH1 : (0 <= e)) (PreH2 : (e <= e_pre)) (PreH3 : (0 <= e_pre)) (PreH4 : (e_pre <= 998244853)) (PreH5 : (0 <= a)) (PreH6 : (a < 998244853)) (PreH7 : (0 <= r)) (PreH8 : (r < 998244853)) (PreH9 : (((r * (Z.pow (a) (e)) ) % ( 998244853 ) ) = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))) (PreH10 : (e = 0)) ,
  (r = ((Z.pow (a_pre) (e_pre)) % ( 998244853 ) ))
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (m_pre: Z) (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 2000)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= 2000)) ,
  ((( &( "N" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
|--
  “ ((n_pre + m_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + m_pre )) ”
.

Definition solver_safety_wit_2 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 2000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 2000)) ,
  ((( &( "ifac" ) )) # Ptr  |->_)
  **  (Int64Array.undef_full retval ((n_pre + m_pre ) + 1 ) )
  **  ((( &( "fac" ) )) # Ptr  |-> retval)
  **  ((( &( "N" ) )) # Int  |-> (n_pre + m_pre ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
|--
  “ (((n_pre + m_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((n_pre + m_pre ) + 1 )) ”
.

Definition solver_safety_wit_3 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 2000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 2000)) ,
  ((( &( "ifac" ) )) # Ptr  |->_)
  **  (Int64Array.undef_full retval ((n_pre + m_pre ) + 1 ) )
  **  ((( &( "fac" ) )) # Ptr  |-> retval)
  **  ((( &( "N" ) )) # Int  |-> (n_pre + m_pre ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_4 := 
forall (m_pre: Z) (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 2000)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= 2000)) ,
  ((( &( "fac" ) )) # Ptr  |->_)
  **  ((( &( "N" ) )) # Int  |-> (n_pre + m_pre ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
|--
  “ (((n_pre + m_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((n_pre + m_pre ) + 1 )) ”
.

Definition solver_safety_wit_5 := 
forall (m_pre: Z) (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 2000)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= 2000)) ,
  ((( &( "fac" ) )) # Ptr  |->_)
  **  ((( &( "N" ) )) # Int  |-> (n_pre + m_pre ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_6 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000)) ,
  (Int64Array.undef_full retval_2 ((n_pre + m_pre ) + 1 ) )
  **  ((( &( "ifac" ) )) # Ptr  |-> retval_2)
  **  (Int64Array.undef_full retval ((n_pre + m_pre ) + 1 ) )
  **  ((( &( "fac" ) )) # Ptr  |-> retval)
  **  ((( &( "N" ) )) # Int  |-> (n_pre + m_pre ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_7 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000)) ,
  (Int64Array.undef_full retval_2 ((n_pre + m_pre ) + 1 ) )
  **  ((( &( "ifac" ) )) # Ptr  |-> retval_2)
  **  (Int64Array.undef_full retval ((n_pre + m_pre ) + 1 ) )
  **  ((( &( "fac" ) )) # Ptr  |-> retval)
  **  ((( &( "N" ) )) # Int  |-> (n_pre + m_pre ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_8 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (((retval + (0 * sizeof(INT64)))) # Int64  |-> 1)
  **  (Int64Array.undef_seg retval 1 ((n_pre + m_pre ) + 1 ) )
  **  (Int64Array.undef_full retval_2 ((n_pre + m_pre ) + 1 ) )
  **  ((( &( "ifac" ) )) # Ptr  |-> retval_2)
  **  ((( &( "fac" ) )) # Ptr  |-> retval)
  **  ((( &( "N" ) )) # Int  |-> (n_pre + m_pre ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_9 := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (i <= N)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000)) (PreH7 : (1 <= i)) (PreH8 : (i <= (N + 1 ))) (PreH9 : ((Zlength (fl)) = i)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((((Znth (j) (fl) (0)) = ((P080Factorial (j)) % ( 998244853 ) )) /\ (0 <= (Znth (j) (fl) (0)))) /\ ((Znth (j) (fl) (0)) < 998244853)))) ,
  (Int64Array.seg fac 0 (i + 1 ) (app (fl) ((cons ((((Znth ((i - 1 ) - 0 ) fl 0) * i ) % ( 998244853 ) )) ((@nil Z))))) )
  **  (Int64Array.undef_seg fac (i + 1 ) (N + 1 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.undef_full ifac (N + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_10 := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (i <= N)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000)) (PreH7 : (1 <= i)) (PreH8 : (i <= (N + 1 ))) (PreH9 : ((Zlength (fl)) = i)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((((Znth (j) (fl) (0)) = ((P080Factorial (j)) % ( 998244853 ) )) /\ (0 <= (Znth (j) (fl) (0)))) /\ ((Znth (j) (fl) (0)) < 998244853)))) ,
  (Int64Array.seg fac 0 i fl )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.undef_seg fac i (N + 1 ) )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.undef_full ifac (N + 1 ) )
|--
  “ ((((Znth ((i - 1 ) - 0 ) fl 0) * i ) <> (INT64_MIN)) \/ (998244853 <> (-1))) ” 
  &&  “ (998244853 <> 0) ”
.

Definition solver_safety_wit_11 := 
(
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (i <= N)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000)) (PreH7 : (1 <= i)) (PreH8 : (i <= (N + 1 ))) (PreH9 : ((Zlength (fl)) = i)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((((Znth (j) (fl) (0)) = ((P080Factorial (j)) % ( 998244853 ) )) /\ (0 <= (Znth (j) (fl) (0)))) /\ ((Znth (j) (fl) (0)) < 998244853)))) ,
  (Int64Array.seg fac 0 i fl )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.undef_seg fac i (N + 1 ) )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.undef_full ifac (N + 1 ) )
|--
  “ (((Znth ((i - 1 ) - 0 ) fl 0) * i ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ((i - 1 ) - 0 ) fl 0) * i )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (i <= N)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000)) (PreH7 : (1 <= i)) (PreH8 : (i <= (N + 1 ))) (PreH9 : ((Zlength (fl)) = i)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((((Znth (j) (fl) (0)) = ((P080Factorial (j)) % ( 998244853 ) )) /\ (0 <= (Znth (j) (fl) (0)))) /\ ((Znth (j) (fl) (0)) < 998244853)))) ,
  (Int64Array.seg fac 0 i fl )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.undef_seg fac i (N + 1 ) )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.undef_full ifac (N + 1 ) )
|--
  “ (((Znth ((i - 1 ) - 0 ) fl 0) * i ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ((i - 1 ) - 0 ) fl 0) * i )) ”
).

Definition solver_safety_wit_11_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (i <= N)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000)) (PreH7 : (1 <= i)) (PreH8 : (i <= (N + 1 ))) (PreH9 : ((Zlength (fl)) = i)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((((Znth (j) (fl) (0)) = ((P080Factorial (j)) % ( 998244853 ) )) /\ (0 <= (Znth (j) (fl) (0)))) /\ ((Znth (j) (fl) (0)) < 998244853)))) ,
  (Int64Array.seg fac 0 i fl )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.undef_seg fac i (N + 1 ) )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.undef_full ifac (N + 1 ) )
|--
  “ (((Znth ((i - 1 ) - 0 ) fl 0) * i ) <= INT64_MAX) ”
.

Definition solver_safety_wit_11_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (i <= N)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000)) (PreH7 : (1 <= i)) (PreH8 : (i <= (N + 1 ))) (PreH9 : ((Zlength (fl)) = i)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((((Znth (j) (fl) (0)) = ((P080Factorial (j)) % ( 998244853 ) )) /\ (0 <= (Znth (j) (fl) (0)))) /\ ((Znth (j) (fl) (0)) < 998244853)))) ,
  (Int64Array.seg fac 0 i fl )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.undef_seg fac i (N + 1 ) )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.undef_full ifac (N + 1 ) )
|--
  “ ((INT64_MIN) <= ((Znth ((i - 1 ) - 0 ) fl 0) * i )) ”
.

Definition solver_safety_wit_12 := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (i <= N)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000)) (PreH7 : (1 <= i)) (PreH8 : (i <= (N + 1 ))) (PreH9 : ((Zlength (fl)) = i)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((((Znth (j) (fl) (0)) = ((P080Factorial (j)) % ( 998244853 ) )) /\ (0 <= (Znth (j) (fl) (0)))) /\ ((Znth (j) (fl) (0)) < 998244853)))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.seg fac 0 i fl )
  **  (Int64Array.undef_seg fac i (N + 1 ) )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.undef_full ifac (N + 1 ) )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_13 := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (i <= N)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000)) (PreH7 : (1 <= i)) (PreH8 : (i <= (N + 1 ))) (PreH9 : ((Zlength (fl)) = i)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((((Znth (j) (fl) (0)) = ((P080Factorial (j)) % ( 998244853 ) )) /\ (0 <= (Znth (j) (fl) (0)))) /\ ((Znth (j) (fl) (0)) < 998244853)))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.seg fac 0 i fl )
  **  (Int64Array.undef_seg fac i (N + 1 ) )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.undef_full ifac (N + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_14 := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (i <= N)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000)) (PreH7 : (1 <= i)) (PreH8 : (i <= (N + 1 ))) (PreH9 : ((Zlength (fl)) = i)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((((Znth (j) (fl) (0)) = ((P080Factorial (j)) % ( 998244853 ) )) /\ (0 <= (Znth (j) (fl) (0)))) /\ ((Znth (j) (fl) (0)) < 998244853)))) ,
  (Int64Array.seg fac 0 i fl )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.undef_seg fac i (N + 1 ) )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.undef_full ifac (N + 1 ) )
|--
  “ (998244853 <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= 998244853) ”
.

Definition solver_safety_wit_15 := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (i > N)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000)) (PreH7 : (1 <= i)) (PreH8 : (i <= (N + 1 ))) (PreH9 : ((Zlength (fl)) = i)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((((Znth (j) (fl) (0)) = ((P080Factorial (j)) % ( 998244853 ) )) /\ (0 <= (Znth (j) (fl) (0)))) /\ ((Znth (j) (fl) (0)) < 998244853)))) ,
  (Int64Array.seg fac 0 i fl )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.undef_full ifac (N + 1 ) )
|--
  “ ((998244853 - 2 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (998244853 - 2 )) ”
.

Definition solver_safety_wit_16 := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (i > N)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000)) (PreH7 : (1 <= i)) (PreH8 : (i <= (N + 1 ))) (PreH9 : ((Zlength (fl)) = i)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((((Znth (j) (fl) (0)) = ((P080Factorial (j)) % ( 998244853 ) )) /\ (0 <= (Znth (j) (fl) (0)))) /\ ((Znth (j) (fl) (0)) < 998244853)))) ,
  (Int64Array.seg fac 0 i fl )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.undef_full ifac (N + 1 ) )
|--
  “ (998244853 <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= 998244853) ”
.

Definition solver_safety_wit_17 := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (i > N)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000)) (PreH7 : (1 <= i)) (PreH8 : (i <= (N + 1 ))) (PreH9 : ((Zlength (fl)) = i)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((((Znth (j) (fl) (0)) = ((P080Factorial (j)) % ( 998244853 ) )) /\ (0 <= (Znth (j) (fl) (0)))) /\ ((Znth (j) (fl) (0)) < 998244853)))) ,
  (Int64Array.seg fac 0 i fl )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.undef_full ifac (N + 1 ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_18 := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (il: (@list Z)) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (N = (n_pre + m_pre ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 2000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 2000)) (PreH6 : (0 <= i)) (PreH7 : (i <= N)) (PreH8 : ((Zlength (fl)) = (N + 1 ))) (PreH9 : ((Zlength (il)) = ((N + 1 ) - i ))) (PreH10 : (P080Factorials fl (N + 1 ) )) (PreH11 : (P080InverseFactorials il i (N + 1 ) )) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)))) (PreH13 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((N + 1 ) - i ))) -> ((0 <= (Znth (j_2) (il) (0))) /\ ((Znth (j_2) (il) (0)) < 998244853)))) (PreH14 : (i <> 0)) ,
  (Int64Array.undef_seg ifac 0 (i - 1 ) )
  **  (((ifac + ((i - 1 ) * sizeof(INT64)))) # Int64  |-> (((Znth (i - i ) il 0) * i ) % ( 998244853 ) ))
  **  (Int64Array.seg ifac i (N + 1 ) il )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_19 := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (il: (@list Z)) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (N = (n_pre + m_pre ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 2000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 2000)) (PreH6 : (0 <= i)) (PreH7 : (i <= N)) (PreH8 : ((Zlength (fl)) = (N + 1 ))) (PreH9 : ((Zlength (il)) = ((N + 1 ) - i ))) (PreH10 : (P080Factorials fl (N + 1 ) )) (PreH11 : (P080InverseFactorials il i (N + 1 ) )) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)))) (PreH13 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((N + 1 ) - i ))) -> ((0 <= (Znth (j_2) (il) (0))) /\ ((Znth (j_2) (il) (0)) < 998244853)))) (PreH14 : (i <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.undef_seg ifac 0 i )
  **  (Int64Array.seg ifac i (N + 1 ) il )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_20 := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (il: (@list Z)) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (N = (n_pre + m_pre ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 2000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 2000)) (PreH6 : (0 <= i)) (PreH7 : (i <= N)) (PreH8 : ((Zlength (fl)) = (N + 1 ))) (PreH9 : ((Zlength (il)) = ((N + 1 ) - i ))) (PreH10 : (P080Factorials fl (N + 1 ) )) (PreH11 : (P080InverseFactorials il i (N + 1 ) )) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)))) (PreH13 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((N + 1 ) - i ))) -> ((0 <= (Znth (j_2) (il) (0))) /\ ((Znth (j_2) (il) (0)) < 998244853)))) (PreH14 : (i <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.undef_seg ifac 0 i )
  **  (Int64Array.seg ifac i (N + 1 ) il )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_21 := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (il: (@list Z)) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (N = (n_pre + m_pre ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 2000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 2000)) (PreH6 : (0 <= i)) (PreH7 : (i <= N)) (PreH8 : ((Zlength (fl)) = (N + 1 ))) (PreH9 : ((Zlength (il)) = ((N + 1 ) - i ))) (PreH10 : (P080Factorials fl (N + 1 ) )) (PreH11 : (P080InverseFactorials il i (N + 1 ) )) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)))) (PreH13 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((N + 1 ) - i ))) -> ((0 <= (Znth (j_2) (il) (0))) /\ ((Znth (j_2) (il) (0)) < 998244853)))) (PreH14 : (i <> 0)) ,
  (Int64Array.seg ifac i (N + 1 ) il )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.undef_seg ifac 0 i )
|--
  “ ((((Znth (i - i ) il 0) * i ) <> (INT64_MIN)) \/ (998244853 <> (-1))) ” 
  &&  “ (998244853 <> 0) ”
.

Definition solver_safety_wit_22 := 
(
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (il: (@list Z)) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (N = (n_pre + m_pre ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 2000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 2000)) (PreH6 : (0 <= i)) (PreH7 : (i <= N)) (PreH8 : ((Zlength (fl)) = (N + 1 ))) (PreH9 : ((Zlength (il)) = ((N + 1 ) - i ))) (PreH10 : (P080Factorials fl (N + 1 ) )) (PreH11 : (P080InverseFactorials il i (N + 1 ) )) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)))) (PreH13 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((N + 1 ) - i ))) -> ((0 <= (Znth (j_2) (il) (0))) /\ ((Znth (j_2) (il) (0)) < 998244853)))) (PreH14 : (i <> 0)) ,
  (Int64Array.seg ifac i (N + 1 ) il )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.undef_seg ifac 0 i )
|--
  “ (((Znth (i - i ) il 0) * i ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth (i - i ) il 0) * i )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (il: (@list Z)) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (N = (n_pre + m_pre ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 2000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 2000)) (PreH6 : (0 <= i)) (PreH7 : (i <= N)) (PreH8 : ((Zlength (fl)) = (N + 1 ))) (PreH9 : ((Zlength (il)) = ((N + 1 ) - i ))) (PreH10 : (P080Factorials fl (N + 1 ) )) (PreH11 : (P080InverseFactorials il i (N + 1 ) )) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)))) (PreH13 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((N + 1 ) - i ))) -> ((0 <= (Znth (j_2) (il) (0))) /\ ((Znth (j_2) (il) (0)) < 998244853)))) (PreH14 : (i <> 0)) ,
  (Int64Array.seg ifac i (N + 1 ) il )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.undef_seg ifac 0 i )
|--
  “ (((Znth (i - i ) il 0) * i ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth (i - i ) il 0) * i )) ”
).

Definition solver_safety_wit_22_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (il: (@list Z)) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (N = (n_pre + m_pre ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 2000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 2000)) (PreH6 : (0 <= i)) (PreH7 : (i <= N)) (PreH8 : ((Zlength (fl)) = (N + 1 ))) (PreH9 : ((Zlength (il)) = ((N + 1 ) - i ))) (PreH10 : (P080Factorials fl (N + 1 ) )) (PreH11 : (P080InverseFactorials il i (N + 1 ) )) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)))) (PreH13 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((N + 1 ) - i ))) -> ((0 <= (Znth (j_2) (il) (0))) /\ ((Znth (j_2) (il) (0)) < 998244853)))) (PreH14 : (i <> 0)) ,
  (Int64Array.seg ifac i (N + 1 ) il )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.undef_seg ifac 0 i )
|--
  “ (((Znth (i - i ) il 0) * i ) <= INT64_MAX) ”
.

Definition solver_safety_wit_22_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (il: (@list Z)) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (N = (n_pre + m_pre ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 2000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 2000)) (PreH6 : (0 <= i)) (PreH7 : (i <= N)) (PreH8 : ((Zlength (fl)) = (N + 1 ))) (PreH9 : ((Zlength (il)) = ((N + 1 ) - i ))) (PreH10 : (P080Factorials fl (N + 1 ) )) (PreH11 : (P080InverseFactorials il i (N + 1 ) )) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)))) (PreH13 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((N + 1 ) - i ))) -> ((0 <= (Znth (j_2) (il) (0))) /\ ((Znth (j_2) (il) (0)) < 998244853)))) (PreH14 : (i <> 0)) ,
  (Int64Array.seg ifac i (N + 1 ) il )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.undef_seg ifac 0 i )
|--
  “ ((INT64_MIN) <= ((Znth (i - i ) il 0) * i )) ”
.

Definition solver_safety_wit_23 := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (il: (@list Z)) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (N = (n_pre + m_pre ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 2000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 2000)) (PreH6 : (0 <= i)) (PreH7 : (i <= N)) (PreH8 : ((Zlength (fl)) = (N + 1 ))) (PreH9 : ((Zlength (il)) = ((N + 1 ) - i ))) (PreH10 : (P080Factorials fl (N + 1 ) )) (PreH11 : (P080InverseFactorials il i (N + 1 ) )) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)))) (PreH13 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((N + 1 ) - i ))) -> ((0 <= (Znth (j_2) (il) (0))) /\ ((Znth (j_2) (il) (0)) < 998244853)))) (PreH14 : (i <> 0)) ,
  (Int64Array.seg ifac i (N + 1 ) il )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.undef_seg ifac 0 i )
|--
  “ (998244853 <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= 998244853) ”
.

Definition solver_safety_wit_24 := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (il: (@list Z)) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (N = (n_pre + m_pre ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 2000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 2000)) (PreH6 : (0 <= i)) (PreH7 : (i <= N)) (PreH8 : ((Zlength (fl)) = (N + 1 ))) (PreH9 : ((Zlength (il)) = ((N + 1 ) - i ))) (PreH10 : (P080Factorials fl (N + 1 ) )) (PreH11 : (P080InverseFactorials il i (N + 1 ) )) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)))) (PreH13 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((N + 1 ) - i ))) -> ((0 <= (Znth (j_2) (il) (0))) /\ ((Znth (j_2) (il) (0)) < 998244853)))) (PreH14 : (i = 0)) ,
  ((( &( "W" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.undef_seg ifac 0 i )
  **  (Int64Array.seg ifac i (N + 1 ) il )
|--
  “ ((m_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (m_pre + 1 )) ”
.

Definition solver_safety_wit_25 := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (il: (@list Z)) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (N = (n_pre + m_pre ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 2000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 2000)) (PreH6 : (0 <= i)) (PreH7 : (i <= N)) (PreH8 : ((Zlength (fl)) = (N + 1 ))) (PreH9 : ((Zlength (il)) = ((N + 1 ) - i ))) (PreH10 : (P080Factorials fl (N + 1 ) )) (PreH11 : (P080InverseFactorials il i (N + 1 ) )) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)))) (PreH13 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((N + 1 ) - i ))) -> ((0 <= (Znth (j_2) (il) (0))) /\ ((Znth (j_2) (il) (0)) < 998244853)))) (PreH14 : (i = 0)) ,
  ((( &( "W" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.undef_seg ifac 0 i )
  **  (Int64Array.seg ifac i (N + 1 ) il )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_26 := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (il: (@list Z)) (fl: (@list Z)) (i: Z) (N: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000)) (PreH7 : (0 <= i)) (PreH8 : (i <= N)) (PreH9 : ((Zlength (fl)) = (N + 1 ))) (PreH10 : ((Zlength (il)) = ((N + 1 ) - i ))) (PreH11 : (P080Factorials fl (N + 1 ) )) (PreH12 : (P080InverseFactorials il i (N + 1 ) )) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)))) (PreH14 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((N + 1 ) - i ))) -> ((0 <= (Znth (j_2) (il) (0))) /\ ((Znth (j_2) (il) (0)) < 998244853)))) (PreH15 : (i = 0)) ,
  ((( &( "D" ) )) # Ptr  |->_)
  **  (Int64Array.full retval ((n_pre + 1 ) * (m_pre + 1 ) ) (repeat_Z (0) (((n_pre + 1 ) * (m_pre + 1 ) ))) )
  **  ((( &( "K" ) )) # Ptr  |-> retval)
  **  ((( &( "W" ) )) # Int  |-> (m_pre + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.seg ifac i (N + 1 ) il )
|--
  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + 1 )) ”
.

Definition solver_safety_wit_27 := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (il: (@list Z)) (fl: (@list Z)) (i: Z) (N: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000)) (PreH7 : (0 <= i)) (PreH8 : (i <= N)) (PreH9 : ((Zlength (fl)) = (N + 1 ))) (PreH10 : ((Zlength (il)) = ((N + 1 ) - i ))) (PreH11 : (P080Factorials fl (N + 1 ) )) (PreH12 : (P080InverseFactorials il i (N + 1 ) )) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)))) (PreH14 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((N + 1 ) - i ))) -> ((0 <= (Znth (j_2) (il) (0))) /\ ((Znth (j_2) (il) (0)) < 998244853)))) (PreH15 : (i = 0)) ,
  ((( &( "D" ) )) # Ptr  |->_)
  **  (Int64Array.full retval ((n_pre + 1 ) * (m_pre + 1 ) ) (repeat_Z (0) (((n_pre + 1 ) * (m_pre + 1 ) ))) )
  **  ((( &( "K" ) )) # Ptr  |-> retval)
  **  ((( &( "W" ) )) # Int  |-> (m_pre + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.seg ifac i (N + 1 ) il )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_28 := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (il: (@list Z)) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (N = (n_pre + m_pre ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 2000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 2000)) (PreH6 : (0 <= i)) (PreH7 : (i <= N)) (PreH8 : ((Zlength (fl)) = (N + 1 ))) (PreH9 : ((Zlength (il)) = ((N + 1 ) - i ))) (PreH10 : (P080Factorials fl (N + 1 ) )) (PreH11 : (P080InverseFactorials il i (N + 1 ) )) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)))) (PreH13 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((N + 1 ) - i ))) -> ((0 <= (Znth (j_2) (il) (0))) /\ ((Znth (j_2) (il) (0)) < 998244853)))) (PreH14 : (i = 0)) ,
  ((( &( "K" ) )) # Ptr  |->_)
  **  ((( &( "W" ) )) # Int  |-> (m_pre + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.undef_seg ifac 0 i )
  **  (Int64Array.seg ifac i (N + 1 ) il )
|--
  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + 1 )) ”
.

Definition solver_safety_wit_29 := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (il: (@list Z)) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (N = (n_pre + m_pre ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 2000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 2000)) (PreH6 : (0 <= i)) (PreH7 : (i <= N)) (PreH8 : ((Zlength (fl)) = (N + 1 ))) (PreH9 : ((Zlength (il)) = ((N + 1 ) - i ))) (PreH10 : (P080Factorials fl (N + 1 ) )) (PreH11 : (P080InverseFactorials il i (N + 1 ) )) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)))) (PreH13 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((N + 1 ) - i ))) -> ((0 <= (Znth (j_2) (il) (0))) /\ ((Znth (j_2) (il) (0)) < 998244853)))) (PreH14 : (i = 0)) ,
  ((( &( "K" ) )) # Ptr  |->_)
  **  ((( &( "W" ) )) # Int  |-> (m_pre + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.undef_seg ifac 0 i )
  **  (Int64Array.seg ifac i (N + 1 ) il )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_30 := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (il: (@list Z)) (fl: (@list Z)) (i: Z) (N: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (N = (n_pre + m_pre ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 2000)) (PreH8 : (0 <= i)) (PreH9 : (i <= N)) (PreH10 : ((Zlength (fl)) = (N + 1 ))) (PreH11 : ((Zlength (il)) = ((N + 1 ) - i ))) (PreH12 : (P080Factorials fl (N + 1 ) )) (PreH13 : (P080InverseFactorials il i (N + 1 ) )) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((N + 1 ) - i ))) -> ((0 <= (Znth (j_2) (il) (0))) /\ ((Znth (j_2) (il) (0)) < 998244853)))) (PreH16 : (i = 0)) ,
  ((( &( "y" ) )) # Int  |->_)
  **  (Int64Array.full retval_2 ((n_pre + 1 ) * (m_pre + 1 ) ) (repeat_Z (0) (((n_pre + 1 ) * (m_pre + 1 ) ))) )
  **  ((( &( "D" ) )) # Ptr  |-> retval_2)
  **  (Int64Array.full retval ((n_pre + 1 ) * (m_pre + 1 ) ) (repeat_Z (0) (((n_pre + 1 ) * (m_pre + 1 ) ))) )
  **  ((( &( "K" ) )) # Ptr  |-> retval)
  **  ((( &( "W" ) )) # Int  |-> (m_pre + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.seg ifac i (N + 1 ) il )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_31 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= m_pre)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (W = (m_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 2000)) (PreH8 : ((Zlength (fl)) = (N + 1 ))) (PreH9 : ((Zlength (il)) = (N + 1 ))) (PreH10 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH11 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH12 : (P080Factorials fl (N + 1 ) )) (PreH13 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH16 : (0 <= y)) (PreH17 : (y <= (m_pre + 1 ))) (PreH18 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < y)) -> ((Znth (j_3) (kl) (0)) = 1))) (PreH19 : forall (j_4: Z) , (((y <= j_4) /\ (j_4 < ((n_pre + 1 ) * W ))) -> ((Znth (j_4) (kl) (0)) = 0))) (PreH20 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < ((n_pre + 1 ) * W ))) -> ((Znth (j_5) (dl) (0)) = 0))) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((0 * W ) + y )) (1) (kl)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ ((y + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (y + 1 )) ”
.

Definition solver_safety_wit_32 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= m_pre)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (W = (m_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 2000)) (PreH8 : ((Zlength (fl)) = (N + 1 ))) (PreH9 : ((Zlength (il)) = (N + 1 ))) (PreH10 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH11 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH12 : (P080Factorials fl (N + 1 ) )) (PreH13 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH16 : (0 <= y)) (PreH17 : (y <= (m_pre + 1 ))) (PreH18 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < y)) -> ((Znth (j_3) (kl) (0)) = 1))) (PreH19 : forall (j_4: Z) , (((y <= j_4) /\ (j_4 < ((n_pre + 1 ) * W ))) -> ((Znth (j_4) (kl) (0)) = 0))) (PreH20 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < ((n_pre + 1 ) * W ))) -> ((Znth (j_5) (dl) (0)) = 0))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_33 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= m_pre)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (W = (m_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 2000)) (PreH8 : ((Zlength (fl)) = (N + 1 ))) (PreH9 : ((Zlength (il)) = (N + 1 ))) (PreH10 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH11 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH12 : (P080Factorials fl (N + 1 ) )) (PreH13 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH16 : (0 <= y)) (PreH17 : (y <= (m_pre + 1 ))) (PreH18 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < y)) -> ((Znth (j_3) (kl) (0)) = 1))) (PreH19 : forall (j_4: Z) , (((y <= j_4) /\ (j_4 < ((n_pre + 1 ) * W ))) -> ((Znth (j_4) (kl) (0)) = 0))) (PreH20 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < ((n_pre + 1 ) * W ))) -> ((Znth (j_5) (dl) (0)) = 0))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_34 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y > m_pre)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (W = (m_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 2000)) (PreH8 : ((Zlength (fl)) = (N + 1 ))) (PreH9 : ((Zlength (il)) = (N + 1 ))) (PreH10 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH11 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH12 : (P080Factorials fl (N + 1 ) )) (PreH13 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH16 : (0 <= y)) (PreH17 : (y <= (m_pre + 1 ))) (PreH18 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < y)) -> ((Znth (j_3) (kl) (0)) = 1))) (PreH19 : forall (j_4: Z) , (((y <= j_4) /\ (j_4 < ((n_pre + 1 ) * W ))) -> ((Znth (j_4) (kl) (0)) = 0))) (PreH20 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < ((n_pre + 1 ) * W ))) -> ((Znth (j_5) (dl) (0)) = 0))) ,
  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_35 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (0 <= (x * W ))) (PreH2 : ((x * W ) < ((n_pre + 1 ) * W ))) (PreH3 : (N <= INT_MAX)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (N >= INT_MIN)) (PreH6 : (m_pre >= INT_MIN)) (PreH7 : (x <= n_pre)) (PreH8 : (N = (n_pre + m_pre ))) (PreH9 : (W = (m_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 2000)) (PreH12 : (0 <= m_pre)) (PreH13 : (m_pre <= 2000)) (PreH14 : ((Zlength (fl)) = (N + 1 ))) (PreH15 : ((Zlength (il)) = (N + 1 ))) (PreH16 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH17 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH18 : (P080Factorials fl (N + 1 ) )) (PreH19 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH20 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH21 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH22 : (1 <= x)) (PreH23 : (x <= (n_pre + 1 ))) (PreH24 : (P080Tables n_pre m_pre x 0 kl dl )) ,
  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_36 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (0 <= (x * W ))) (PreH2 : ((x * W ) < ((n_pre + 1 ) * W ))) (PreH3 : (N <= INT_MAX)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (N >= INT_MIN)) (PreH6 : (m_pre >= INT_MIN)) (PreH7 : (x <= n_pre)) (PreH8 : (N = (n_pre + m_pre ))) (PreH9 : (W = (m_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 2000)) (PreH12 : (0 <= m_pre)) (PreH13 : (m_pre <= 2000)) (PreH14 : ((Zlength (fl)) = (N + 1 ))) (PreH15 : ((Zlength (il)) = (N + 1 ))) (PreH16 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH17 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH18 : (P080Factorials fl (N + 1 ) )) (PreH19 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH20 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH21 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH22 : (1 <= x)) (PreH23 : (x <= (n_pre + 1 ))) (PreH24 : (P080Tables n_pre m_pre x 0 kl dl )) ,
  ((( &( "y" ) )) # Int  |->_)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + 0 )) (x) (dl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_37 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= y)) (PreH2 : (0 <= ((x * W ) + y ))) (PreH3 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH4 : (0 <= (((x - 1 ) * W ) + y ))) (PreH5 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH7 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH8 : (N <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (N >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (y <= m_pre)) (PreH13 : (N = (n_pre + m_pre ))) (PreH14 : (W = (m_pre + 1 ))) (PreH15 : (0 <= n_pre)) (PreH16 : (n_pre <= 2000)) (PreH17 : (0 <= m_pre)) (PreH18 : (m_pre <= 2000)) (PreH19 : ((Zlength (fl)) = (N + 1 ))) (PreH20 : ((Zlength (il)) = (N + 1 ))) (PreH21 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH22 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH23 : (P080Factorials fl (N + 1 ) )) (PreH24 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH25 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH26 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH27 : (1 <= x)) (PreH28 : (x <= n_pre)) (PreH29 : (1 <= y)) (PreH30 : (y <= (m_pre + 1 ))) (PreH31 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) <> (INT64_MIN)) \/ (998244853 <> (-1))) ” 
  &&  “ (998244853 <> 0) ”
.

Definition solver_safety_wit_38 := 
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= y)) (PreH2 : (0 <= ((x * W ) + y ))) (PreH3 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH4 : (0 <= (((x - 1 ) * W ) + y ))) (PreH5 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH7 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH8 : (N <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (N >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (y <= m_pre)) (PreH13 : (N = (n_pre + m_pre ))) (PreH14 : (W = (m_pre + 1 ))) (PreH15 : (0 <= n_pre)) (PreH16 : (n_pre <= 2000)) (PreH17 : (0 <= m_pre)) (PreH18 : (m_pre <= 2000)) (PreH19 : ((Zlength (fl)) = (N + 1 ))) (PreH20 : ((Zlength (il)) = (N + 1 ))) (PreH21 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH22 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH23 : (P080Factorials fl (N + 1 ) )) (PreH24 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH25 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH26 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH27 : (1 <= x)) (PreH28 : (x <= n_pre)) (PreH29 : (1 <= y)) (PreH30 : (y <= (m_pre + 1 ))) (PreH31 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= y)) (PreH2 : (0 <= ((x * W ) + y ))) (PreH3 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH4 : (0 <= (((x - 1 ) * W ) + y ))) (PreH5 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH7 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH8 : (N <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (N >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (y <= m_pre)) (PreH13 : (N = (n_pre + m_pre ))) (PreH14 : (W = (m_pre + 1 ))) (PreH15 : (0 <= n_pre)) (PreH16 : (n_pre <= 2000)) (PreH17 : (0 <= m_pre)) (PreH18 : (m_pre <= 2000)) (PreH19 : ((Zlength (fl)) = (N + 1 ))) (PreH20 : ((Zlength (il)) = (N + 1 ))) (PreH21 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH22 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH23 : (P080Factorials fl (N + 1 ) )) (PreH24 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH25 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH26 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH27 : (1 <= x)) (PreH28 : (x <= n_pre)) (PreH29 : (1 <= y)) (PreH30 : (y <= (m_pre + 1 ))) (PreH31 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) )) ”
).

Definition solver_safety_wit_38_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= y)) (PreH2 : (0 <= ((x * W ) + y ))) (PreH3 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH4 : (0 <= (((x - 1 ) * W ) + y ))) (PreH5 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH7 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH8 : (N <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (N >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (y <= m_pre)) (PreH13 : (N = (n_pre + m_pre ))) (PreH14 : (W = (m_pre + 1 ))) (PreH15 : (0 <= n_pre)) (PreH16 : (n_pre <= 2000)) (PreH17 : (0 <= m_pre)) (PreH18 : (m_pre <= 2000)) (PreH19 : ((Zlength (fl)) = (N + 1 ))) (PreH20 : ((Zlength (il)) = (N + 1 ))) (PreH21 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH22 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH23 : (P080Factorials fl (N + 1 ) )) (PreH24 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH25 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH26 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH27 : (1 <= x)) (PreH28 : (x <= n_pre)) (PreH29 : (1 <= y)) (PreH30 : (y <= (m_pre + 1 ))) (PreH31 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_38_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= y)) (PreH2 : (0 <= ((x * W ) + y ))) (PreH3 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH4 : (0 <= (((x - 1 ) * W ) + y ))) (PreH5 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH7 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH8 : (N <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (N >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (y <= m_pre)) (PreH13 : (N = (n_pre + m_pre ))) (PreH14 : (W = (m_pre + 1 ))) (PreH15 : (0 <= n_pre)) (PreH16 : (n_pre <= 2000)) (PreH17 : (0 <= m_pre)) (PreH18 : (m_pre <= 2000)) (PreH19 : ((Zlength (fl)) = (N + 1 ))) (PreH20 : ((Zlength (il)) = (N + 1 ))) (PreH21 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH22 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH23 : (P080Factorials fl (N + 1 ) )) (PreH24 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH25 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH26 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH27 : (1 <= x)) (PreH28 : (x <= n_pre)) (PreH29 : (1 <= y)) (PreH30 : (y <= (m_pre + 1 ))) (PreH31 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ ((INT64_MIN) <= ((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) )) ”
.

Definition solver_safety_wit_39 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= y)) (PreH2 : (0 <= ((x * W ) + y ))) (PreH3 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH4 : (0 <= (((x - 1 ) * W ) + y ))) (PreH5 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH7 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH8 : (N <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (N >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (y <= m_pre)) (PreH13 : (N = (n_pre + m_pre ))) (PreH14 : (W = (m_pre + 1 ))) (PreH15 : (0 <= n_pre)) (PreH16 : (n_pre <= 2000)) (PreH17 : (0 <= m_pre)) (PreH18 : (m_pre <= 2000)) (PreH19 : ((Zlength (fl)) = (N + 1 ))) (PreH20 : ((Zlength (il)) = (N + 1 ))) (PreH21 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH22 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH23 : (P080Factorials fl (N + 1 ) )) (PreH24 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH25 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH26 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH27 : (1 <= x)) (PreH28 : (x <= n_pre)) (PreH29 : (1 <= y)) (PreH30 : (y <= (m_pre + 1 ))) (PreH31 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ ((y - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (y - 1 )) ”
.

Definition solver_safety_wit_40 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= y)) (PreH2 : (0 <= ((x * W ) + y ))) (PreH3 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH4 : (0 <= (((x - 1 ) * W ) + y ))) (PreH5 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH7 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH8 : (N <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (N >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (y <= m_pre)) (PreH13 : (N = (n_pre + m_pre ))) (PreH14 : (W = (m_pre + 1 ))) (PreH15 : (0 <= n_pre)) (PreH16 : (n_pre <= 2000)) (PreH17 : (0 <= m_pre)) (PreH18 : (m_pre <= 2000)) (PreH19 : ((Zlength (fl)) = (N + 1 ))) (PreH20 : ((Zlength (il)) = (N + 1 ))) (PreH21 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH22 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH23 : (P080Factorials fl (N + 1 ) )) (PreH24 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH25 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH26 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH27 : (1 <= x)) (PreH28 : (x <= n_pre)) (PreH29 : (1 <= y)) (PreH30 : (y <= (m_pre + 1 ))) (PreH31 : (P080Tables n_pre m_pre x y kl dl )) ,
  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ ((x - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x - 1 )) ”
.

Definition solver_safety_wit_41 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= y)) (PreH2 : (0 <= ((x * W ) + y ))) (PreH3 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH4 : (0 <= (((x - 1 ) * W ) + y ))) (PreH5 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH7 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH8 : (N <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (N >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (y <= m_pre)) (PreH13 : (N = (n_pre + m_pre ))) (PreH14 : (W = (m_pre + 1 ))) (PreH15 : (0 <= n_pre)) (PreH16 : (n_pre <= 2000)) (PreH17 : (0 <= m_pre)) (PreH18 : (m_pre <= 2000)) (PreH19 : ((Zlength (fl)) = (N + 1 ))) (PreH20 : ((Zlength (il)) = (N + 1 ))) (PreH21 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH22 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH23 : (P080Factorials fl (N + 1 ) )) (PreH24 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH25 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH26 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH27 : (1 <= x)) (PreH28 : (x <= n_pre)) (PreH29 : (1 <= y)) (PreH30 : (y <= (m_pre + 1 ))) (PreH31 : (P080Tables n_pre m_pre x y kl dl )) ,
  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_42 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= y)) (PreH2 : (0 <= ((x * W ) + y ))) (PreH3 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH4 : (0 <= (((x - 1 ) * W ) + y ))) (PreH5 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH7 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH8 : (N <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (N >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (y <= m_pre)) (PreH13 : (N = (n_pre + m_pre ))) (PreH14 : (W = (m_pre + 1 ))) (PreH15 : (0 <= n_pre)) (PreH16 : (n_pre <= 2000)) (PreH17 : (0 <= m_pre)) (PreH18 : (m_pre <= 2000)) (PreH19 : ((Zlength (fl)) = (N + 1 ))) (PreH20 : ((Zlength (il)) = (N + 1 ))) (PreH21 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH22 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH23 : (P080Factorials fl (N + 1 ) )) (PreH24 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH25 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH26 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH27 : (1 <= x)) (PreH28 : (x <= n_pre)) (PreH29 : (1 <= y)) (PreH30 : (y <= (m_pre + 1 ))) (PreH31 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_43 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= y)) (PreH2 : (0 <= ((x * W ) + y ))) (PreH3 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH4 : (0 <= (((x - 1 ) * W ) + y ))) (PreH5 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH7 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH8 : (N <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (N >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (y <= m_pre)) (PreH13 : (N = (n_pre + m_pre ))) (PreH14 : (W = (m_pre + 1 ))) (PreH15 : (0 <= n_pre)) (PreH16 : (n_pre <= 2000)) (PreH17 : (0 <= m_pre)) (PreH18 : (m_pre <= 2000)) (PreH19 : ((Zlength (fl)) = (N + 1 ))) (PreH20 : ((Zlength (il)) = (N + 1 ))) (PreH21 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH22 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH23 : (P080Factorials fl (N + 1 ) )) (PreH24 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH25 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH26 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH27 : (1 <= x)) (PreH28 : (x <= n_pre)) (PreH29 : (1 <= y)) (PreH30 : (y <= (m_pre + 1 ))) (PreH31 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (998244853 <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= 998244853) ”
.

Definition solver_safety_wit_44 := 
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) 0) )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) 0) )) ”
).

Definition solver_safety_wit_44_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_44_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((INT64_MIN) <= (((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) 0) )) ”
.

Definition solver_safety_wit_45 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((y - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (y - 1 )) ”
.

Definition solver_safety_wit_46 := 
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) )) ”
).

Definition solver_safety_wit_46_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_46_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((INT64_MIN) <= ((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) )) ”
.

Definition solver_safety_wit_47 := 
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) )) ”
).

Definition solver_safety_wit_47_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_47_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((INT64_MIN) <= (((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) )) ”
.

Definition solver_safety_wit_48 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((y - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (y - 1 )) ”
.

Definition solver_safety_wit_49 := 
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) )) ”
).

Definition solver_safety_wit_49_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_49_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((INT64_MIN) <= ((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) )) ”
.

Definition solver_safety_wit_50 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ ((x - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x - 1 )) ”
.

Definition solver_safety_wit_51 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= y)) (PreH2 : (0 <= ((x * W ) + y ))) (PreH3 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH4 : (0 <= (((x - 1 ) * W ) + y ))) (PreH5 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH7 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH8 : (N <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (N >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (y <= m_pre)) (PreH13 : (N = (n_pre + m_pre ))) (PreH14 : (W = (m_pre + 1 ))) (PreH15 : (0 <= n_pre)) (PreH16 : (n_pre <= 2000)) (PreH17 : (0 <= m_pre)) (PreH18 : (m_pre <= 2000)) (PreH19 : ((Zlength (fl)) = (N + 1 ))) (PreH20 : ((Zlength (il)) = (N + 1 ))) (PreH21 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH22 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH23 : (P080Factorials fl (N + 1 ) )) (PreH24 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH25 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH26 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH27 : (1 <= x)) (PreH28 : (x <= n_pre)) (PreH29 : (1 <= y)) (PreH30 : (y <= (m_pre + 1 ))) (PreH31 : (P080Tables n_pre m_pre x y kl dl )) ,
  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_52 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y < 0)) (PreH2 : (x <= y)) (PreH3 : (0 <= ((x * W ) + y ))) (PreH4 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH5 : (0 <= (((x - 1 ) * W ) + y ))) (PreH6 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH7 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH8 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH9 : (N <= INT_MAX)) (PreH10 : (m_pre <= INT_MAX)) (PreH11 : (N >= INT_MIN)) (PreH12 : (m_pre >= INT_MIN)) (PreH13 : (y <= m_pre)) (PreH14 : (N = (n_pre + m_pre ))) (PreH15 : (W = (m_pre + 1 ))) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 2000)) (PreH18 : (0 <= m_pre)) (PreH19 : (m_pre <= 2000)) (PreH20 : ((Zlength (fl)) = (N + 1 ))) (PreH21 : ((Zlength (il)) = (N + 1 ))) (PreH22 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH23 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH24 : (P080Factorials fl (N + 1 ) )) (PreH25 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH26 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH27 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH28 : (1 <= x)) (PreH29 : (x <= n_pre)) (PreH30 : (1 <= y)) (PreH31 : (y <= (m_pre + 1 ))) (PreH32 : (P080Tables n_pre m_pre x y kl dl )) ,
  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ False ”
.

Definition solver_safety_wit_53 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y >= 0)) (PreH2 : (x <= y)) (PreH3 : (0 <= ((x * W ) + y ))) (PreH4 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH5 : (0 <= (((x - 1 ) * W ) + y ))) (PreH6 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH7 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH8 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH9 : (N <= INT_MAX)) (PreH10 : (m_pre <= INT_MAX)) (PreH11 : (N >= INT_MIN)) (PreH12 : (m_pre >= INT_MIN)) (PreH13 : (y <= m_pre)) (PreH14 : (N = (n_pre + m_pre ))) (PreH15 : (W = (m_pre + 1 ))) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 2000)) (PreH18 : (0 <= m_pre)) (PreH19 : (m_pre <= 2000)) (PreH20 : ((Zlength (fl)) = (N + 1 ))) (PreH21 : ((Zlength (il)) = (N + 1 ))) (PreH22 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH23 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH24 : (P080Factorials fl (N + 1 ) )) (PreH25 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH26 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH27 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH28 : (1 <= x)) (PreH29 : (x <= n_pre)) (PreH30 : (1 <= y)) (PreH31 : (y <= (m_pre + 1 ))) (PreH32 : (P080Tables n_pre m_pre x y kl dl )) ,
  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (((x + y ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((x + y ) - 1 )) ”
.

Definition solver_safety_wit_54 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y >= 0)) (PreH2 : (x <= y)) (PreH3 : (0 <= ((x * W ) + y ))) (PreH4 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH5 : (0 <= (((x - 1 ) * W ) + y ))) (PreH6 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH7 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH8 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH9 : (N <= INT_MAX)) (PreH10 : (m_pre <= INT_MAX)) (PreH11 : (N >= INT_MIN)) (PreH12 : (m_pre >= INT_MIN)) (PreH13 : (y <= m_pre)) (PreH14 : (N = (n_pre + m_pre ))) (PreH15 : (W = (m_pre + 1 ))) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 2000)) (PreH18 : (0 <= m_pre)) (PreH19 : (m_pre <= 2000)) (PreH20 : ((Zlength (fl)) = (N + 1 ))) (PreH21 : ((Zlength (il)) = (N + 1 ))) (PreH22 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH23 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH24 : (P080Factorials fl (N + 1 ) )) (PreH25 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH26 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH27 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH28 : (1 <= x)) (PreH29 : (x <= n_pre)) (PreH30 : (1 <= y)) (PreH31 : (y <= (m_pre + 1 ))) (PreH32 : (P080Tables n_pre m_pre x y kl dl )) ,
  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ ((x + y ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x + y )) ”
.

Definition solver_safety_wit_55 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y >= 0)) (PreH2 : (x <= y)) (PreH3 : (0 <= ((x * W ) + y ))) (PreH4 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH5 : (0 <= (((x - 1 ) * W ) + y ))) (PreH6 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH7 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH8 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH9 : (N <= INT_MAX)) (PreH10 : (m_pre <= INT_MAX)) (PreH11 : (N >= INT_MIN)) (PreH12 : (m_pre >= INT_MIN)) (PreH13 : (y <= m_pre)) (PreH14 : (N = (n_pre + m_pre ))) (PreH15 : (W = (m_pre + 1 ))) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 2000)) (PreH18 : (0 <= m_pre)) (PreH19 : (m_pre <= 2000)) (PreH20 : ((Zlength (fl)) = (N + 1 ))) (PreH21 : ((Zlength (il)) = (N + 1 ))) (PreH22 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH23 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH24 : (P080Factorials fl (N + 1 ) )) (PreH25 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH26 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH27 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH28 : (1 <= x)) (PreH29 : (x <= n_pre)) (PreH30 : (1 <= y)) (PreH31 : (y <= (m_pre + 1 ))) (PreH32 : (P080Tables n_pre m_pre x y kl dl )) ,
  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_56 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y > ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ False ”
.

Definition solver_safety_wit_57 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ ((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) <> (INT64_MIN)) \/ (998244853 <> (-1))) ” 
  &&  “ (998244853 <> 0) ”
.

Definition solver_safety_wit_58 := 
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) )) ”
).

Definition solver_safety_wit_58_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_58_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ ((INT64_MIN) <= ((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) )) ”
.

Definition solver_safety_wit_59 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ ((((x + y ) - 1 ) - y ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((x + y ) - 1 ) - y )) ”
.

Definition solver_safety_wit_60 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (((x + y ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((x + y ) - 1 )) ”
.

Definition solver_safety_wit_61 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ ((x + y ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x + y )) ”
.

Definition solver_safety_wit_62 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ ((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) <> (INT64_MIN)) \/ (998244853 <> (-1))) ” 
  &&  “ (998244853 <> 0) ”
.

Definition solver_safety_wit_63 := 
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) )) ”
).

Definition solver_safety_wit_63_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_63_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ ((INT64_MIN) <= ((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) )) ”
.

Definition solver_safety_wit_64 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (((x + y ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((x + y ) - 1 )) ”
.

Definition solver_safety_wit_65 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ ((x + y ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x + y )) ”
.

Definition solver_safety_wit_66 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_67 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (998244853 <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= 998244853) ”
.

Definition solver_safety_wit_68 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_69 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (998244853 <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= 998244853) ”
.

Definition solver_safety_wit_70 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_71 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_72 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_73 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x < 0)) (PreH2 : (y <= ((x + y ) - 1 ))) (PreH3 : (y >= 0)) (PreH4 : (x <= y)) (PreH5 : (0 <= ((x * W ) + y ))) (PreH6 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH7 : (0 <= (((x - 1 ) * W ) + y ))) (PreH8 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH9 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH10 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH11 : (N <= INT_MAX)) (PreH12 : (m_pre <= INT_MAX)) (PreH13 : (N >= INT_MIN)) (PreH14 : (m_pre >= INT_MIN)) (PreH15 : (y <= m_pre)) (PreH16 : (N = (n_pre + m_pre ))) (PreH17 : (W = (m_pre + 1 ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 2000)) (PreH20 : (0 <= m_pre)) (PreH21 : (m_pre <= 2000)) (PreH22 : ((Zlength (fl)) = (N + 1 ))) (PreH23 : ((Zlength (il)) = (N + 1 ))) (PreH24 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH25 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH26 : (P080Factorials fl (N + 1 ) )) (PreH27 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH28 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH29 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH30 : (1 <= x)) (PreH31 : (x <= n_pre)) (PreH32 : (1 <= y)) (PreH33 : (y <= (m_pre + 1 ))) (PreH34 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ False ”
.

Definition solver_safety_wit_74 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x >= 0)) (PreH2 : (y <= ((x + y ) - 1 ))) (PreH3 : (y >= 0)) (PreH4 : (x <= y)) (PreH5 : (0 <= ((x * W ) + y ))) (PreH6 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH7 : (0 <= (((x - 1 ) * W ) + y ))) (PreH8 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH9 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH10 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH11 : (N <= INT_MAX)) (PreH12 : (m_pre <= INT_MAX)) (PreH13 : (N >= INT_MIN)) (PreH14 : (m_pre >= INT_MIN)) (PreH15 : (y <= m_pre)) (PreH16 : (N = (n_pre + m_pre ))) (PreH17 : (W = (m_pre + 1 ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 2000)) (PreH20 : (0 <= m_pre)) (PreH21 : (m_pre <= 2000)) (PreH22 : ((Zlength (fl)) = (N + 1 ))) (PreH23 : ((Zlength (il)) = (N + 1 ))) (PreH24 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH25 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH26 : (P080Factorials fl (N + 1 ) )) (PreH27 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH28 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH29 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH30 : (1 <= x)) (PreH31 : (x <= n_pre)) (PreH32 : (1 <= y)) (PreH33 : (y <= (m_pre + 1 ))) (PreH34 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (((x + y ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((x + y ) - 1 )) ”
.

Definition solver_safety_wit_75 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x >= 0)) (PreH2 : (y <= ((x + y ) - 1 ))) (PreH3 : (y >= 0)) (PreH4 : (x <= y)) (PreH5 : (0 <= ((x * W ) + y ))) (PreH6 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH7 : (0 <= (((x - 1 ) * W ) + y ))) (PreH8 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH9 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH10 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH11 : (N <= INT_MAX)) (PreH12 : (m_pre <= INT_MAX)) (PreH13 : (N >= INT_MIN)) (PreH14 : (m_pre >= INT_MIN)) (PreH15 : (y <= m_pre)) (PreH16 : (N = (n_pre + m_pre ))) (PreH17 : (W = (m_pre + 1 ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 2000)) (PreH20 : (0 <= m_pre)) (PreH21 : (m_pre <= 2000)) (PreH22 : ((Zlength (fl)) = (N + 1 ))) (PreH23 : ((Zlength (il)) = (N + 1 ))) (PreH24 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH25 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH26 : (P080Factorials fl (N + 1 ) )) (PreH27 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH28 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH29 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH30 : (1 <= x)) (PreH31 : (x <= n_pre)) (PreH32 : (1 <= y)) (PreH33 : (y <= (m_pre + 1 ))) (PreH34 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((x + y ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x + y )) ”
.

Definition solver_safety_wit_76 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x >= 0)) (PreH2 : (y <= ((x + y ) - 1 ))) (PreH3 : (y >= 0)) (PreH4 : (x <= y)) (PreH5 : (0 <= ((x * W ) + y ))) (PreH6 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH7 : (0 <= (((x - 1 ) * W ) + y ))) (PreH8 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH9 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH10 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH11 : (N <= INT_MAX)) (PreH12 : (m_pre <= INT_MAX)) (PreH13 : (N >= INT_MIN)) (PreH14 : (m_pre >= INT_MIN)) (PreH15 : (y <= m_pre)) (PreH16 : (N = (n_pre + m_pre ))) (PreH17 : (W = (m_pre + 1 ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 2000)) (PreH20 : (0 <= m_pre)) (PreH21 : (m_pre <= 2000)) (PreH22 : ((Zlength (fl)) = (N + 1 ))) (PreH23 : ((Zlength (il)) = (N + 1 ))) (PreH24 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH25 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH26 : (P080Factorials fl (N + 1 ) )) (PreH27 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH28 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH29 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH30 : (1 <= x)) (PreH31 : (x <= n_pre)) (PreH32 : (1 <= y)) (PreH33 : (y <= (m_pre + 1 ))) (PreH34 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_77 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x > ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ False ”
.

Definition solver_safety_wit_78 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) <> (INT64_MIN)) \/ (998244853 <> (-1))) ” 
  &&  “ (998244853 <> 0) ”
.

Definition solver_safety_wit_79 := 
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) )) ”
).

Definition solver_safety_wit_79_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_79_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((INT64_MIN) <= ((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) )) ”
.

Definition solver_safety_wit_80 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((((x + y ) - 1 ) - x ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((x + y ) - 1 ) - x )) ”
.

Definition solver_safety_wit_81 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (((x + y ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((x + y ) - 1 )) ”
.

Definition solver_safety_wit_82 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((x + y ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x + y )) ”
.

Definition solver_safety_wit_83 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) <> (INT64_MIN)) \/ (998244853 <> (-1))) ” 
  &&  “ (998244853 <> 0) ”
.

Definition solver_safety_wit_84 := 
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) )) ”
).

Definition solver_safety_wit_84_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_84_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((INT64_MIN) <= ((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) )) ”
.

Definition solver_safety_wit_85 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (((x + y ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((x + y ) - 1 )) ”
.

Definition solver_safety_wit_86 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((x + y ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x + y )) ”
.

Definition solver_safety_wit_87 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_88 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (998244853 <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= 998244853) ”
.

Definition solver_safety_wit_89 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_90 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (998244853 <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= 998244853) ”
.

Definition solver_safety_wit_91 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_92 := 
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) kl 0) )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) kl 0) )) ”
).

Definition solver_safety_wit_92_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_92_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((INT64_MIN) <= (((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) kl 0) )) ”
.

Definition solver_safety_wit_93 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((y - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (y - 1 )) ”
.

Definition solver_safety_wit_94 := 
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) )) ”
).

Definition solver_safety_wit_94_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_94_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((INT64_MIN) <= ((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) )) ”
.

Definition solver_safety_wit_95 := 
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) )) ”
).

Definition solver_safety_wit_95_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_95_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((INT64_MIN) <= (((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) )) ”
.

Definition solver_safety_wit_96 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((y - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (y - 1 )) ”
.

Definition solver_safety_wit_97 := 
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) )) ”
).

Definition solver_safety_wit_97_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_97_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((INT64_MIN) <= ((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) )) ”
.

Definition solver_safety_wit_98 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ ((x - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x - 1 )) ”
.

Definition solver_safety_wit_99 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x > y)) (PreH2 : (0 <= ((x * W ) + y ))) (PreH3 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH4 : (0 <= (((x - 1 ) * W ) + y ))) (PreH5 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH7 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH8 : (N <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (N >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (y <= m_pre)) (PreH13 : (N = (n_pre + m_pre ))) (PreH14 : (W = (m_pre + 1 ))) (PreH15 : (0 <= n_pre)) (PreH16 : (n_pre <= 2000)) (PreH17 : (0 <= m_pre)) (PreH18 : (m_pre <= 2000)) (PreH19 : ((Zlength (fl)) = (N + 1 ))) (PreH20 : ((Zlength (il)) = (N + 1 ))) (PreH21 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH22 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH23 : (P080Factorials fl (N + 1 ) )) (PreH24 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH25 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH26 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH27 : (1 <= x)) (PreH28 : (x <= n_pre)) (PreH29 : (1 <= y)) (PreH30 : (y <= (m_pre + 1 ))) (PreH31 : (P080Tables n_pre m_pre x y kl dl )) ,
  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_100 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y < 0)) (PreH2 : (x > y)) (PreH3 : (0 <= ((x * W ) + y ))) (PreH4 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH5 : (0 <= (((x - 1 ) * W ) + y ))) (PreH6 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH7 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH8 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH9 : (N <= INT_MAX)) (PreH10 : (m_pre <= INT_MAX)) (PreH11 : (N >= INT_MIN)) (PreH12 : (m_pre >= INT_MIN)) (PreH13 : (y <= m_pre)) (PreH14 : (N = (n_pre + m_pre ))) (PreH15 : (W = (m_pre + 1 ))) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 2000)) (PreH18 : (0 <= m_pre)) (PreH19 : (m_pre <= 2000)) (PreH20 : ((Zlength (fl)) = (N + 1 ))) (PreH21 : ((Zlength (il)) = (N + 1 ))) (PreH22 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH23 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH24 : (P080Factorials fl (N + 1 ) )) (PreH25 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH26 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH27 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH28 : (1 <= x)) (PreH29 : (x <= n_pre)) (PreH30 : (1 <= y)) (PreH31 : (y <= (m_pre + 1 ))) (PreH32 : (P080Tables n_pre m_pre x y kl dl )) ,
  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ False ”
.

Definition solver_safety_wit_101 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y >= 0)) (PreH2 : (x > y)) (PreH3 : (0 <= ((x * W ) + y ))) (PreH4 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH5 : (0 <= (((x - 1 ) * W ) + y ))) (PreH6 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH7 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH8 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH9 : (N <= INT_MAX)) (PreH10 : (m_pre <= INT_MAX)) (PreH11 : (N >= INT_MIN)) (PreH12 : (m_pre >= INT_MIN)) (PreH13 : (y <= m_pre)) (PreH14 : (N = (n_pre + m_pre ))) (PreH15 : (W = (m_pre + 1 ))) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 2000)) (PreH18 : (0 <= m_pre)) (PreH19 : (m_pre <= 2000)) (PreH20 : ((Zlength (fl)) = (N + 1 ))) (PreH21 : ((Zlength (il)) = (N + 1 ))) (PreH22 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH23 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH24 : (P080Factorials fl (N + 1 ) )) (PreH25 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH26 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH27 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH28 : (1 <= x)) (PreH29 : (x <= n_pre)) (PreH30 : (1 <= y)) (PreH31 : (y <= (m_pre + 1 ))) (PreH32 : (P080Tables n_pre m_pre x y kl dl )) ,
  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (((x + y ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((x + y ) - 1 )) ”
.

Definition solver_safety_wit_102 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y >= 0)) (PreH2 : (x > y)) (PreH3 : (0 <= ((x * W ) + y ))) (PreH4 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH5 : (0 <= (((x - 1 ) * W ) + y ))) (PreH6 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH7 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH8 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH9 : (N <= INT_MAX)) (PreH10 : (m_pre <= INT_MAX)) (PreH11 : (N >= INT_MIN)) (PreH12 : (m_pre >= INT_MIN)) (PreH13 : (y <= m_pre)) (PreH14 : (N = (n_pre + m_pre ))) (PreH15 : (W = (m_pre + 1 ))) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 2000)) (PreH18 : (0 <= m_pre)) (PreH19 : (m_pre <= 2000)) (PreH20 : ((Zlength (fl)) = (N + 1 ))) (PreH21 : ((Zlength (il)) = (N + 1 ))) (PreH22 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH23 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH24 : (P080Factorials fl (N + 1 ) )) (PreH25 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH26 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH27 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH28 : (1 <= x)) (PreH29 : (x <= n_pre)) (PreH30 : (1 <= y)) (PreH31 : (y <= (m_pre + 1 ))) (PreH32 : (P080Tables n_pre m_pre x y kl dl )) ,
  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ ((x + y ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x + y )) ”
.

Definition solver_safety_wit_103 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y >= 0)) (PreH2 : (x > y)) (PreH3 : (0 <= ((x * W ) + y ))) (PreH4 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH5 : (0 <= (((x - 1 ) * W ) + y ))) (PreH6 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH7 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH8 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH9 : (N <= INT_MAX)) (PreH10 : (m_pre <= INT_MAX)) (PreH11 : (N >= INT_MIN)) (PreH12 : (m_pre >= INT_MIN)) (PreH13 : (y <= m_pre)) (PreH14 : (N = (n_pre + m_pre ))) (PreH15 : (W = (m_pre + 1 ))) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 2000)) (PreH18 : (0 <= m_pre)) (PreH19 : (m_pre <= 2000)) (PreH20 : ((Zlength (fl)) = (N + 1 ))) (PreH21 : ((Zlength (il)) = (N + 1 ))) (PreH22 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH23 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH24 : (P080Factorials fl (N + 1 ) )) (PreH25 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH26 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH27 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH28 : (1 <= x)) (PreH29 : (x <= n_pre)) (PreH30 : (1 <= y)) (PreH31 : (y <= (m_pre + 1 ))) (PreH32 : (P080Tables n_pre m_pre x y kl dl )) ,
  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_104 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y > ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ False ”
.

Definition solver_safety_wit_105 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ ((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) <> (INT64_MIN)) \/ (998244853 <> (-1))) ” 
  &&  “ (998244853 <> 0) ”
.

Definition solver_safety_wit_106 := 
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) )) ”
).

Definition solver_safety_wit_106_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_106_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ ((INT64_MIN) <= ((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) )) ”
.

Definition solver_safety_wit_107 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ ((((x + y ) - 1 ) - y ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((x + y ) - 1 ) - y )) ”
.

Definition solver_safety_wit_108 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (((x + y ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((x + y ) - 1 )) ”
.

Definition solver_safety_wit_109 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ ((x + y ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x + y )) ”
.

Definition solver_safety_wit_110 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ ((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) <> (INT64_MIN)) \/ (998244853 <> (-1))) ” 
  &&  “ (998244853 <> 0) ”
.

Definition solver_safety_wit_111 := 
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) )) ”
).

Definition solver_safety_wit_111_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_111_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ ((INT64_MIN) <= ((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) )) ”
.

Definition solver_safety_wit_112 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (((x + y ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((x + y ) - 1 )) ”
.

Definition solver_safety_wit_113 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ ((x + y ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x + y )) ”
.

Definition solver_safety_wit_114 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_115 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (998244853 <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= 998244853) ”
.

Definition solver_safety_wit_116 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_117 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (998244853 <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= 998244853) ”
.

Definition solver_safety_wit_118 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_119 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_120 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_121 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x < 0)) (PreH2 : (y <= ((x + y ) - 1 ))) (PreH3 : (y >= 0)) (PreH4 : (x > y)) (PreH5 : (0 <= ((x * W ) + y ))) (PreH6 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH7 : (0 <= (((x - 1 ) * W ) + y ))) (PreH8 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH9 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH10 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH11 : (N <= INT_MAX)) (PreH12 : (m_pre <= INT_MAX)) (PreH13 : (N >= INT_MIN)) (PreH14 : (m_pre >= INT_MIN)) (PreH15 : (y <= m_pre)) (PreH16 : (N = (n_pre + m_pre ))) (PreH17 : (W = (m_pre + 1 ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 2000)) (PreH20 : (0 <= m_pre)) (PreH21 : (m_pre <= 2000)) (PreH22 : ((Zlength (fl)) = (N + 1 ))) (PreH23 : ((Zlength (il)) = (N + 1 ))) (PreH24 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH25 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH26 : (P080Factorials fl (N + 1 ) )) (PreH27 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH28 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH29 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH30 : (1 <= x)) (PreH31 : (x <= n_pre)) (PreH32 : (1 <= y)) (PreH33 : (y <= (m_pre + 1 ))) (PreH34 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ False ”
.

Definition solver_safety_wit_122 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x >= 0)) (PreH2 : (y <= ((x + y ) - 1 ))) (PreH3 : (y >= 0)) (PreH4 : (x > y)) (PreH5 : (0 <= ((x * W ) + y ))) (PreH6 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH7 : (0 <= (((x - 1 ) * W ) + y ))) (PreH8 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH9 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH10 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH11 : (N <= INT_MAX)) (PreH12 : (m_pre <= INT_MAX)) (PreH13 : (N >= INT_MIN)) (PreH14 : (m_pre >= INT_MIN)) (PreH15 : (y <= m_pre)) (PreH16 : (N = (n_pre + m_pre ))) (PreH17 : (W = (m_pre + 1 ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 2000)) (PreH20 : (0 <= m_pre)) (PreH21 : (m_pre <= 2000)) (PreH22 : ((Zlength (fl)) = (N + 1 ))) (PreH23 : ((Zlength (il)) = (N + 1 ))) (PreH24 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH25 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH26 : (P080Factorials fl (N + 1 ) )) (PreH27 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH28 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH29 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH30 : (1 <= x)) (PreH31 : (x <= n_pre)) (PreH32 : (1 <= y)) (PreH33 : (y <= (m_pre + 1 ))) (PreH34 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (((x + y ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((x + y ) - 1 )) ”
.

Definition solver_safety_wit_123 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x >= 0)) (PreH2 : (y <= ((x + y ) - 1 ))) (PreH3 : (y >= 0)) (PreH4 : (x > y)) (PreH5 : (0 <= ((x * W ) + y ))) (PreH6 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH7 : (0 <= (((x - 1 ) * W ) + y ))) (PreH8 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH9 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH10 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH11 : (N <= INT_MAX)) (PreH12 : (m_pre <= INT_MAX)) (PreH13 : (N >= INT_MIN)) (PreH14 : (m_pre >= INT_MIN)) (PreH15 : (y <= m_pre)) (PreH16 : (N = (n_pre + m_pre ))) (PreH17 : (W = (m_pre + 1 ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 2000)) (PreH20 : (0 <= m_pre)) (PreH21 : (m_pre <= 2000)) (PreH22 : ((Zlength (fl)) = (N + 1 ))) (PreH23 : ((Zlength (il)) = (N + 1 ))) (PreH24 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH25 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH26 : (P080Factorials fl (N + 1 ) )) (PreH27 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH28 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH29 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH30 : (1 <= x)) (PreH31 : (x <= n_pre)) (PreH32 : (1 <= y)) (PreH33 : (y <= (m_pre + 1 ))) (PreH34 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((x + y ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x + y )) ”
.

Definition solver_safety_wit_124 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x >= 0)) (PreH2 : (y <= ((x + y ) - 1 ))) (PreH3 : (y >= 0)) (PreH4 : (x > y)) (PreH5 : (0 <= ((x * W ) + y ))) (PreH6 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH7 : (0 <= (((x - 1 ) * W ) + y ))) (PreH8 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH9 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH10 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH11 : (N <= INT_MAX)) (PreH12 : (m_pre <= INT_MAX)) (PreH13 : (N >= INT_MIN)) (PreH14 : (m_pre >= INT_MIN)) (PreH15 : (y <= m_pre)) (PreH16 : (N = (n_pre + m_pre ))) (PreH17 : (W = (m_pre + 1 ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 2000)) (PreH20 : (0 <= m_pre)) (PreH21 : (m_pre <= 2000)) (PreH22 : ((Zlength (fl)) = (N + 1 ))) (PreH23 : ((Zlength (il)) = (N + 1 ))) (PreH24 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH25 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH26 : (P080Factorials fl (N + 1 ) )) (PreH27 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH28 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH29 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH30 : (1 <= x)) (PreH31 : (x <= n_pre)) (PreH32 : (1 <= y)) (PreH33 : (y <= (m_pre + 1 ))) (PreH34 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_125 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x > ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ False ”
.

Definition solver_safety_wit_126 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) <> (INT64_MIN)) \/ (998244853 <> (-1))) ” 
  &&  “ (998244853 <> 0) ”
.

Definition solver_safety_wit_127 := 
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) )) ”
).

Definition solver_safety_wit_127_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_127_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((INT64_MIN) <= ((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) )) ”
.

Definition solver_safety_wit_128 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((((x + y ) - 1 ) - x ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((x + y ) - 1 ) - x )) ”
.

Definition solver_safety_wit_129 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (((x + y ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((x + y ) - 1 )) ”
.

Definition solver_safety_wit_130 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((x + y ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x + y )) ”
.

Definition solver_safety_wit_131 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) <> (INT64_MIN)) \/ (998244853 <> (-1))) ” 
  &&  “ (998244853 <> 0) ”
.

Definition solver_safety_wit_132 := 
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) )) ”
).

Definition solver_safety_wit_132_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_132_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((INT64_MIN) <= ((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) )) ”
.

Definition solver_safety_wit_133 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (((x + y ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((x + y ) - 1 )) ”
.

Definition solver_safety_wit_134 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((x + y ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x + y )) ”
.

Definition solver_safety_wit_135 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_136 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (998244853 <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= 998244853) ”
.

Definition solver_safety_wit_137 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_138 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (998244853 <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= 998244853) ”
.

Definition solver_safety_wit_139 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_140 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |-> (((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) 0) ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (((((((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) 0) ) % ( 998244853 ) ) + 998244853 ) <> (INT64_MIN)) \/ (998244853 <> (-1))) ” 
  &&  “ (998244853 <> 0) ”
.

Definition solver_safety_wit_141 := 
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |-> (((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) 0) ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((((((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) 0) ) % ( 998244853 ) ) + 998244853 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) 0) ) % ( 998244853 ) ) + 998244853 )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |-> (((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) 0) ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((((((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) 0) ) % ( 998244853 ) ) + 998244853 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) 0) ) % ( 998244853 ) ) + 998244853 )) ”
).

Definition solver_safety_wit_141_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |-> (((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) 0) ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((((((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) 0) ) % ( 998244853 ) ) + 998244853 ) <= INT64_MAX) ”
.

Definition solver_safety_wit_141_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |-> (((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) 0) ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((INT64_MIN) <= (((((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) 0) ) % ( 998244853 ) ) + 998244853 )) ”
.

Definition solver_safety_wit_142 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |-> (((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) 0) ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (((((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) 0) ) <> (INT64_MIN)) \/ (998244853 <> (-1))) ” 
  &&  “ (998244853 <> 0) ”
.

Definition solver_safety_wit_143 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |-> (((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) 0) ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (998244853 <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= 998244853) ”
.

Definition solver_safety_wit_144 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |-> (((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) 0) ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (998244853 <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= 998244853) ”
.

Definition solver_safety_wit_145 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |-> (((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) 0) ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (998244853 <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= 998244853) ”
.

Definition solver_safety_wit_146 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |-> (((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (((((((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) ) + 998244853 ) <> (INT64_MIN)) \/ (998244853 <> (-1))) ” 
  &&  “ (998244853 <> 0) ”
.

Definition solver_safety_wit_147 := 
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |-> (((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((((((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) ) + 998244853 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) ) + 998244853 )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |-> (((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((((((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) ) + 998244853 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) ) + 998244853 )) ”
).

Definition solver_safety_wit_147_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |-> (((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((((((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) ) + 998244853 ) <= INT64_MAX) ”
.

Definition solver_safety_wit_147_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |-> (((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((INT64_MIN) <= (((((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) ) + 998244853 )) ”
.

Definition solver_safety_wit_148 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |-> (((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (((((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) <> (INT64_MIN)) \/ (998244853 <> (-1))) ” 
  &&  “ (998244853 <> 0) ”
.

Definition solver_safety_wit_149 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |-> (((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (998244853 <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= 998244853) ”
.

Definition solver_safety_wit_150 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |-> (((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (998244853 <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= 998244853) ”
.

Definition solver_safety_wit_151 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  ((( &( "val" ) )) # Int64  |-> (((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ (998244853 <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= 998244853) ”
.

Definition solver_safety_wit_152 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) (((((((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) 0) ) % ( 998244853 ) ) + 998244853 ) % ( 998244853 ) )) (dl)) )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((y + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (y + 1 )) ”
.

Definition solver_safety_wit_153 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) (((((((((((((Znth ((x + y ) - 1 ) fl 0) * (Znth y il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl 0) ) - (((((Znth ((x + y ) - 1 ) fl 0) * (Znth x il 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) ) + 998244853 ) % ( 998244853 ) )) (dl)) )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  ((( &( "D" ) )) # Ptr  |-> D)
|--
  “ ((y + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (y + 1 )) ”
.

Definition solver_safety_wit_154 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y > m_pre)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (W = (m_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 2000)) (PreH8 : ((Zlength (fl)) = (N + 1 ))) (PreH9 : ((Zlength (il)) = (N + 1 ))) (PreH10 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH11 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH12 : (P080Factorials fl (N + 1 ) )) (PreH13 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH16 : (1 <= x)) (PreH17 : (x <= n_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= (m_pre + 1 ))) (PreH20 : (P080Tables n_pre m_pre x y kl dl )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ ((x + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (m_pre: Z) (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000)) ,
  (((retval + (0 * sizeof(INT64)))) # Int64  |-> 1)
  **  (Int64Array.undef_seg retval 1 ((n_pre + m_pre ) + 1 ) )
  **  (Int64Array.undef_full retval_2 ((n_pre + m_pre ) + 1 ) )
|--
  EX (fl: (@list Z)) ,
  “ ((n_pre + m_pre ) = (n_pre + m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= ((n_pre + m_pre ) + 1 )) ” 
  &&  “ ((Zlength (fl)) = 1) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < 1)) -> ((((Znth (j) (fl) (0)) = ((P080Factorial (j)) % ( 998244853 ) )) /\ (0 <= (Znth (j) (fl) (0)))) /\ ((Znth (j) (fl) (0)) < 998244853))) ”
  &&  (Int64Array.seg retval 0 1 fl )
  **  (Int64Array.undef_seg retval 1 ((n_pre + m_pre ) + 1 ) )
  **  (Int64Array.undef_full retval_2 ((n_pre + m_pre ) + 1 ) )
) \/
(
forall (m_pre: Z) (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (1 <= INT64_MAX)) (PreH2 : (1 >= INT64_MIN)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 2000)) (PreH7 : (0 <= m_pre)) (PreH8 : (m_pre <= 2000)) ,
  (((retval + (0 * sizeof(INT64)))) # Int64  |-> 1)
|--
  EX (fl: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= ((n_pre + m_pre ) + 1 )) ” 
  &&  “ ((Zlength (fl)) = 1) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < 1)) -> ((((Znth (j) (fl) (0)) = ((P080Factorial (j)) % ( 998244853 ) )) /\ (0 <= (Znth (j) (fl) (0)))) /\ ((Znth (j) (fl) (0)) < 998244853))) ”
  &&  (Int64Array.seg retval 0 1 fl )
).

Definition solver_entail_wit_2 := 
(
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (fl_2: (@list Z)) (i: Z) (N: Z) (PreH1 : (i <= N)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000)) (PreH7 : (1 <= i)) (PreH8 : (i <= (N + 1 ))) (PreH9 : ((Zlength (fl_2)) = i)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((((Znth (j) (fl_2) (0)) = ((P080Factorial (j)) % ( 998244853 ) )) /\ (0 <= (Znth (j) (fl_2) (0)))) /\ ((Znth (j) (fl_2) (0)) < 998244853)))) ,
  (Int64Array.seg fac 0 (i + 1 ) (app (fl_2) ((cons ((((Znth ((i - 1 ) - 0 ) fl_2 0) * i ) % ( 998244853 ) )) ((@nil Z))))) )
  **  (Int64Array.undef_seg fac (i + 1 ) (N + 1 ) )
  **  (Int64Array.undef_full ifac (N + 1 ) )
|--
  EX (fl: (@list Z)) ,
  “ (N = (n_pre + m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (N + 1 )) ” 
  &&  “ ((Zlength (fl)) = (i + 1 )) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (i + 1 ))) -> ((((Znth (j) (fl) (0)) = ((P080Factorial (j)) % ( 998244853 ) )) /\ (0 <= (Znth (j) (fl) (0)))) /\ ((Znth (j) (fl) (0)) < 998244853))) ”
  &&  (Int64Array.seg fac 0 (i + 1 ) fl )
  **  (Int64Array.undef_seg fac (i + 1 ) (N + 1 ) )
  **  (Int64Array.undef_full ifac (N + 1 ) )
) \/
(
forall (m_pre: Z) (n_pre: Z) (fl_2: (@list Z)) (i: Z) (N: Z) (PreH1 : (i <= N)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000)) (PreH7 : (1 <= i)) (PreH8 : (i <= (N + 1 ))) (PreH9 : ((Zlength (fl_2)) = i)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((((Znth (j) (fl_2) (0)) = ((P080Factorial (j)) % ( 998244853 ) )) /\ (0 <= (Znth (j) (fl_2) (0)))) /\ ((Znth (j) (fl_2) (0)) < 998244853)))) ,
  TT && emp 
|--
  “ ((Zlength ((app (fl_2) ((cons ((((Znth ((i - 1 ) - 0 ) fl_2 0) * i ) % ( 998244853 ) )) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (fl_2: (@list Z)) (i: Z) (N: Z) (PreH1 : (i <= N)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000)) (PreH7 : (1 <= i)) (PreH8 : (i <= (N + 1 ))) (PreH9 : ((Zlength (fl_2)) = i)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((((Znth (j) (fl_2) (0)) = ((P080Factorial (j)) % ( 998244853 ) )) /\ (0 <= (Znth (j) (fl_2) (0)))) /\ ((Znth (j) (fl_2) (0)) < 998244853)))) ,
  ((Zlength ((app (fl_2) ((cons ((((Znth ((i - 1 ) - 0 ) fl_2 0) * i ) % ( 998244853 ) )) ((@nil Z))))))) = (i + 1 ))
.

Definition solver_entail_wit_3 := 
(
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (fl_2: (@list Z)) (i: Z) (N: Z) (retval: Z) (PreH1 : (retval = ((Z.pow ((Znth (N - 0 ) fl_2 0)) ((998244853 - 2 ))) % ( 998244853 ) ))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 998244853)) (PreH4 : (i > N)) (PreH5 : (N = (n_pre + m_pre ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (0 <= m_pre)) (PreH9 : (m_pre <= 2000)) (PreH10 : (1 <= i)) (PreH11 : (i <= (N + 1 ))) (PreH12 : ((Zlength (fl_2)) = i)) (PreH13 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < i)) -> ((((Znth (j_3) (fl_2) (0)) = ((P080Factorial (j_3)) % ( 998244853 ) )) /\ (0 <= (Znth (j_3) (fl_2) (0)))) /\ ((Znth (j_3) (fl_2) (0)) < 998244853)))) ,
  (Int64Array.undef_seg ifac 0 N )
  **  (((ifac + (N * sizeof(INT64)))) # Int64  |-> retval)
  **  (Int64Array.seg fac 0 i fl_2 )
|--
  EX (il: (@list Z))  (fl: (@list Z)) ,
  “ (N = (n_pre + m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ (0 <= N) ” 
  &&  “ (N <= N) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = ((N + 1 ) - N )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il N (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((N + 1 ) - N ))) -> ((0 <= (Znth (j_2) (il) (0))) /\ ((Znth (j_2) (il) (0)) < 998244853))) ”
  &&  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.undef_seg ifac 0 N )
  **  (Int64Array.seg ifac N (N + 1 ) il )
) \/
(
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (fl_2: (@list Z)) (i: Z) (N: Z) (retval: Z) (PreH1 : (retval <= INT64_MAX)) (PreH2 : (retval >= INT64_MIN)) (PreH3 : (retval = ((Z.pow ((Znth (N - 0 ) fl_2 0)) ((998244853 - 2 ))) % ( 998244853 ) ))) (PreH4 : (0 <= retval)) (PreH5 : (retval < 998244853)) (PreH6 : (i > N)) (PreH7 : (N = (n_pre + m_pre ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : (0 <= m_pre)) (PreH11 : (m_pre <= 2000)) (PreH12 : (1 <= i)) (PreH13 : (i <= (N + 1 ))) (PreH14 : ((Zlength (fl_2)) = i)) (PreH15 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < i)) -> ((((Znth (j_3) (fl_2) (0)) = ((P080Factorial (j_3)) % ( 998244853 ) )) /\ (0 <= (Znth (j_3) (fl_2) (0)))) /\ ((Znth (j_3) (fl_2) (0)) < 998244853)))) ,
  (((ifac + (N * sizeof(INT64)))) # Int64  |-> retval)
  **  (Int64Array.seg fac 0 i fl_2 )
|--
  EX (il: (@list Z))  (fl: (@list Z)) ,
  “ (N = (n_pre + m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ (0 <= N) ” 
  &&  “ (N <= N) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = ((N + 1 ) - N )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il N (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((N + 1 ) - N ))) -> ((0 <= (Znth (j_2) (il) (0))) /\ ((Znth (j_2) (il) (0)) < 998244853))) ”
  &&  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.seg ifac N (N + 1 ) il )
).

Definition solver_entail_wit_4 := 
(
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (il_2: (@list Z)) (fl_2: (@list Z)) (i: Z) (N: Z) (PreH1 : (N = (n_pre + m_pre ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 2000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 2000)) (PreH6 : (0 <= i)) (PreH7 : (i <= N)) (PreH8 : ((Zlength (fl_2)) = (N + 1 ))) (PreH9 : ((Zlength (il_2)) = ((N + 1 ) - i ))) (PreH10 : (P080Factorials fl_2 (N + 1 ) )) (PreH11 : (P080InverseFactorials il_2 i (N + 1 ) )) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((0 <= (Znth (j) (fl_2) (0))) /\ ((Znth (j) (fl_2) (0)) < 998244853)))) (PreH13 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((N + 1 ) - i ))) -> ((0 <= (Znth (j_2) (il_2) (0))) /\ ((Znth (j_2) (il_2) (0)) < 998244853)))) (PreH14 : (i <> 0)) ,
  (Int64Array.undef_seg ifac 0 (i - 1 ) )
  **  (((ifac + ((i - 1 ) * sizeof(INT64)))) # Int64  |-> (((Znth (i - i ) il_2 0) * i ) % ( 998244853 ) ))
  **  (Int64Array.seg ifac i (N + 1 ) il_2 )
  **  (Int64Array.full fac (N + 1 ) fl_2 )
|--
  EX (il: (@list Z))  (fl: (@list Z)) ,
  “ (N = (n_pre + m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= N) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = ((N + 1 ) - (i - 1 ) )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il (i - 1 ) (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((N + 1 ) - (i - 1 ) ))) -> ((0 <= (Znth (j_2) (il) (0))) /\ ((Znth (j_2) (il) (0)) < 998244853))) ”
  &&  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.undef_seg ifac 0 (i - 1 ) )
  **  (Int64Array.seg ifac (i - 1 ) (N + 1 ) il )
) \/
(
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (il_2: (@list Z)) (fl_2: (@list Z)) (i: Z) (N: Z) (PreH1 : ((((Znth (i - i ) il_2 0) * i ) % ( 998244853 ) ) <= INT64_MAX)) (PreH2 : ((((Znth (i - i ) il_2 0) * i ) % ( 998244853 ) ) >= INT64_MIN)) (PreH3 : (N = (n_pre + m_pre ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 2000)) (PreH8 : (0 <= i)) (PreH9 : (i <= N)) (PreH10 : ((Zlength (fl_2)) = (N + 1 ))) (PreH11 : ((Zlength (il_2)) = ((N + 1 ) - i ))) (PreH12 : (P080Factorials fl_2 (N + 1 ) )) (PreH13 : (P080InverseFactorials il_2 i (N + 1 ) )) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((0 <= (Znth (j) (fl_2) (0))) /\ ((Znth (j) (fl_2) (0)) < 998244853)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((N + 1 ) - i ))) -> ((0 <= (Znth (j_2) (il_2) (0))) /\ ((Znth (j_2) (il_2) (0)) < 998244853)))) (PreH16 : (i <> 0)) ,
  (((ifac + ((i - 1 ) * sizeof(INT64)))) # Int64  |-> (((Znth (i - i ) il_2 0) * i ) % ( 998244853 ) ))
  **  (Int64Array.seg ifac i (N + 1 ) il_2 )
|--
  EX (il: (@list Z)) ,
  “ (N = (n_pre + m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= N) ” 
  &&  “ ((Zlength (fl_2)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = ((N + 1 ) - (i - 1 ) )) ” 
  &&  “ (P080Factorials fl_2 (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il (i - 1 ) (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((0 <= (Znth (j) (fl_2) (0))) /\ ((Znth (j) (fl_2) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((N + 1 ) - (i - 1 ) ))) -> ((0 <= (Znth (j_2) (il) (0))) /\ ((Znth (j_2) (il) (0)) < 998244853))) ”
  &&  (Int64Array.seg ifac (i - 1 ) (N + 1 ) il )
).

Definition solver_entail_wit_5 := 
(
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (il_2: (@list Z)) (fl_2: (@list Z)) (i: Z) (N: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (N = (n_pre + m_pre ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 2000)) (PreH8 : (0 <= i)) (PreH9 : (i <= N)) (PreH10 : ((Zlength (fl_2)) = (N + 1 ))) (PreH11 : ((Zlength (il_2)) = ((N + 1 ) - i ))) (PreH12 : (P080Factorials fl_2 (N + 1 ) )) (PreH13 : (P080InverseFactorials il_2 i (N + 1 ) )) (PreH14 : forall (j_6: Z) , (((0 <= j_6) /\ (j_6 < (N + 1 ))) -> ((0 <= (Znth (j_6) (fl_2) (0))) /\ ((Znth (j_6) (fl_2) (0)) < 998244853)))) (PreH15 : forall (j_7: Z) , (((0 <= j_7) /\ (j_7 < ((N + 1 ) - i ))) -> ((0 <= (Znth (j_7) (il_2) (0))) /\ ((Znth (j_7) (il_2) (0)) < 998244853)))) (PreH16 : (i = 0)) ,
  (Int64Array.full retval_2 ((n_pre + 1 ) * (m_pre + 1 ) ) (repeat_Z (0) (((n_pre + 1 ) * (m_pre + 1 ) ))) )
  **  (Int64Array.full retval ((n_pre + 1 ) * (m_pre + 1 ) ) (repeat_Z (0) (((n_pre + 1 ) * (m_pre + 1 ) ))) )
  **  (Int64Array.full fac (N + 1 ) fl_2 )
  **  (Int64Array.seg ifac i (N + 1 ) il_2 )
|--
  EX (dl: (@list Z))  (kl: (@list Z))  (il: (@list Z))  (fl: (@list Z)) ,
  “ (N = (n_pre + m_pre )) ” 
  &&  “ ((m_pre + 1 ) = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * (m_pre + 1 ) )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * (m_pre + 1 ) )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * (m_pre + 1 ) ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (m_pre + 1 )) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < 0)) -> ((Znth (j_3) (kl) (0)) = 1)) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < ((n_pre + 1 ) * (m_pre + 1 ) ))) -> ((Znth (j_4) (kl) (0)) = 0)) ” 
  &&  “ forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < ((n_pre + 1 ) * (m_pre + 1 ) ))) -> ((Znth (j_5) (dl) (0)) = 0)) ”
  &&  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full retval ((n_pre + 1 ) * (m_pre + 1 ) ) kl )
  **  (Int64Array.full retval_2 ((n_pre + 1 ) * (m_pre + 1 ) ) dl )
) \/
(
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (il_2: (@list Z)) (fl_2: (@list Z)) (i: Z) (N: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (N = (n_pre + m_pre ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 2000)) (PreH8 : (0 <= i)) (PreH9 : (i <= N)) (PreH10 : ((Zlength (fl_2)) = (N + 1 ))) (PreH11 : ((Zlength (il_2)) = ((N + 1 ) - i ))) (PreH12 : (P080Factorials fl_2 (N + 1 ) )) (PreH13 : (P080InverseFactorials il_2 i (N + 1 ) )) (PreH14 : forall (j_6: Z) , (((0 <= j_6) /\ (j_6 < (N + 1 ))) -> ((0 <= (Znth (j_6) (fl_2) (0))) /\ ((Znth (j_6) (fl_2) (0)) < 998244853)))) (PreH15 : forall (j_7: Z) , (((0 <= j_7) /\ (j_7 < ((N + 1 ) - i ))) -> ((0 <= (Znth (j_7) (il_2) (0))) /\ ((Znth (j_7) (il_2) (0)) < 998244853)))) (PreH16 : (i = 0)) ,
  (Int64Array.seg ifac i (N + 1 ) il_2 )
|--
  EX (il: (@list Z)) ,
  “ (N = (n_pre + m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl_2)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength ((repeat_Z (0) (((n_pre + 1 ) * (m_pre + 1 ) ))))) = ((n_pre + 1 ) * (m_pre + 1 ) )) ” 
  &&  “ ((Zlength ((repeat_Z (0) (((n_pre + 1 ) * (m_pre + 1 ) ))))) = ((n_pre + 1 ) * (m_pre + 1 ) )) ” 
  &&  “ (P080Factorials fl_2 (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl_2) (0))) /\ ((Znth (j) (fl_2) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * (m_pre + 1 ) ))) -> ((((0 <= (Znth (j_2) ((repeat_Z (0) (((n_pre + 1 ) * (m_pre + 1 ) )))) (0))) /\ ((Znth (j_2) ((repeat_Z (0) (((n_pre + 1 ) * (m_pre + 1 ) )))) (0)) < 998244853)) /\ (0 <= (Znth (j_2) ((repeat_Z (0) (((n_pre + 1 ) * (m_pre + 1 ) )))) (0)))) /\ ((Znth (j_2) ((repeat_Z (0) (((n_pre + 1 ) * (m_pre + 1 ) )))) (0)) < 998244853))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (m_pre + 1 )) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < 0)) -> ((Znth (j_3) ((repeat_Z (0) (((n_pre + 1 ) * (m_pre + 1 ) )))) (0)) = 1)) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < ((n_pre + 1 ) * (m_pre + 1 ) ))) -> ((Znth (j_4) ((repeat_Z (0) (((n_pre + 1 ) * (m_pre + 1 ) )))) (0)) = 0)) ” 
  &&  “ forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < ((n_pre + 1 ) * (m_pre + 1 ) ))) -> ((Znth (j_5) ((repeat_Z (0) (((n_pre + 1 ) * (m_pre + 1 ) )))) (0)) = 0)) ”
  &&  (Int64Array.full ifac (N + 1 ) il )
).

Definition solver_entail_wit_6 := 
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (dl_2: (@list Z)) (kl_2: (@list Z)) (il_2: (@list Z)) (fl_2: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= m_pre)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (W = (m_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 2000)) (PreH8 : ((Zlength (fl_2)) = (N + 1 ))) (PreH9 : ((Zlength (il_2)) = (N + 1 ))) (PreH10 : ((Zlength (kl_2)) = ((n_pre + 1 ) * W ))) (PreH11 : ((Zlength (dl_2)) = ((n_pre + 1 ) * W ))) (PreH12 : (P080Factorials fl_2 (N + 1 ) )) (PreH13 : (P080InverseFactorials il_2 0 (N + 1 ) )) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl_2) (0))) /\ ((Znth (j) (fl_2) (0)) < 998244853)) /\ (0 <= (Znth (j) (il_2) (0)))) /\ ((Znth (j) (il_2) (0)) < 998244853)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl_2) (0))) /\ ((Znth (j_2) (kl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl_2) (0)))) /\ ((Znth (j_2) (dl_2) (0)) < 998244853)))) (PreH16 : (0 <= y)) (PreH17 : (y <= (m_pre + 1 ))) (PreH18 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < y)) -> ((Znth (j_3) (kl_2) (0)) = 1))) (PreH19 : forall (j_4: Z) , (((y <= j_4) /\ (j_4 < ((n_pre + 1 ) * W ))) -> ((Znth (j_4) (kl_2) (0)) = 0))) (PreH20 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < ((n_pre + 1 ) * W ))) -> ((Znth (j_5) (dl_2) (0)) = 0))) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((0 * W ) + y )) (1) (kl_2)) )
  **  (Int64Array.full fac (N + 1 ) fl_2 )
  **  (Int64Array.full ifac (N + 1 ) il_2 )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl_2 )
|--
  EX (dl: (@list Z))  (kl: (@list Z))  (il: (@list Z))  (fl: (@list Z)) ,
  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (0 <= (y + 1 )) ” 
  &&  “ ((y + 1 ) <= (m_pre + 1 )) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (y + 1 ))) -> ((Znth (j_3) (kl) (0)) = 1)) ” 
  &&  “ forall (j_4: Z) , ((((y + 1 ) <= j_4) /\ (j_4 < ((n_pre + 1 ) * W ))) -> ((Znth (j_4) (kl) (0)) = 0)) ” 
  &&  “ forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < ((n_pre + 1 ) * W ))) -> ((Znth (j_5) (dl) (0)) = 0)) ”
  &&  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
) \/
(
forall (m_pre: Z) (n_pre: Z) (y: Z) (dl_2: (@list Z)) (kl_2: (@list Z)) (il_2: (@list Z)) (fl_2: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= m_pre)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (W = (m_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 2000)) (PreH8 : ((Zlength (fl_2)) = (N + 1 ))) (PreH9 : ((Zlength (il_2)) = (N + 1 ))) (PreH10 : ((Zlength (kl_2)) = ((n_pre + 1 ) * W ))) (PreH11 : ((Zlength (dl_2)) = ((n_pre + 1 ) * W ))) (PreH12 : (P080Factorials fl_2 (N + 1 ) )) (PreH13 : (P080InverseFactorials il_2 0 (N + 1 ) )) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl_2) (0))) /\ ((Znth (j) (fl_2) (0)) < 998244853)) /\ (0 <= (Znth (j) (il_2) (0)))) /\ ((Znth (j) (il_2) (0)) < 998244853)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl_2) (0))) /\ ((Znth (j_2) (kl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl_2) (0)))) /\ ((Znth (j_2) (dl_2) (0)) < 998244853)))) (PreH16 : (0 <= y)) (PreH17 : (y <= (m_pre + 1 ))) (PreH18 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < y)) -> ((Znth (j_3) (kl_2) (0)) = 1))) (PreH19 : forall (j_4: Z) , (((y <= j_4) /\ (j_4 < ((n_pre + 1 ) * W ))) -> ((Znth (j_4) (kl_2) (0)) = 0))) (PreH20 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < ((n_pre + 1 ) * W ))) -> ((Znth (j_5) (dl_2) (0)) = 0))) ,
  TT && emp 
|--
  “ ((Zlength ((replace_Znth (((0 * (m_pre + 1 ) ) + y )) (1) (kl_2)))) = ((n_pre + 1 ) * (m_pre + 1 ) )) ”
  &&  emp
).

Definition solver_entail_wit_6_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (y: Z) (dl_2: (@list Z)) (kl_2: (@list Z)) (il_2: (@list Z)) (fl_2: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= m_pre)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (W = (m_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 2000)) (PreH8 : ((Zlength (fl_2)) = (N + 1 ))) (PreH9 : ((Zlength (il_2)) = (N + 1 ))) (PreH10 : ((Zlength (kl_2)) = ((n_pre + 1 ) * W ))) (PreH11 : ((Zlength (dl_2)) = ((n_pre + 1 ) * W ))) (PreH12 : (P080Factorials fl_2 (N + 1 ) )) (PreH13 : (P080InverseFactorials il_2 0 (N + 1 ) )) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl_2) (0))) /\ ((Znth (j) (fl_2) (0)) < 998244853)) /\ (0 <= (Znth (j) (il_2) (0)))) /\ ((Znth (j) (il_2) (0)) < 998244853)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl_2) (0))) /\ ((Znth (j_2) (kl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl_2) (0)))) /\ ((Znth (j_2) (dl_2) (0)) < 998244853)))) (PreH16 : (0 <= y)) (PreH17 : (y <= (m_pre + 1 ))) (PreH18 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < y)) -> ((Znth (j_3) (kl_2) (0)) = 1))) (PreH19 : forall (j_4: Z) , (((y <= j_4) /\ (j_4 < ((n_pre + 1 ) * W ))) -> ((Znth (j_4) (kl_2) (0)) = 0))) (PreH20 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < ((n_pre + 1 ) * W ))) -> ((Znth (j_5) (dl_2) (0)) = 0))) ,
  ((Zlength ((replace_Znth (((0 * (m_pre + 1 ) ) + y )) (1) (kl_2)))) = ((n_pre + 1 ) * (m_pre + 1 ) ))
.

Definition solver_entail_wit_7 := 
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (dl_2: (@list Z)) (kl_2: (@list Z)) (il_2: (@list Z)) (fl_2: (@list Z)) (W: Z) (N: Z) (PreH1 : (y > m_pre)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (W = (m_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 2000)) (PreH8 : ((Zlength (fl_2)) = (N + 1 ))) (PreH9 : ((Zlength (il_2)) = (N + 1 ))) (PreH10 : ((Zlength (kl_2)) = ((n_pre + 1 ) * W ))) (PreH11 : ((Zlength (dl_2)) = ((n_pre + 1 ) * W ))) (PreH12 : (P080Factorials fl_2 (N + 1 ) )) (PreH13 : (P080InverseFactorials il_2 0 (N + 1 ) )) (PreH14 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (N + 1 ))) -> ((((0 <= (Znth (j_3) (fl_2) (0))) /\ ((Znth (j_3) (fl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_3) (il_2) (0)))) /\ ((Znth (j_3) (il_2) (0)) < 998244853)))) (PreH15 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_4) (kl_2) (0))) /\ ((Znth (j_4) (kl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_4) (dl_2) (0)))) /\ ((Znth (j_4) (dl_2) (0)) < 998244853)))) (PreH16 : (0 <= y)) (PreH17 : (y <= (m_pre + 1 ))) (PreH18 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < y)) -> ((Znth (j_5) (kl_2) (0)) = 1))) (PreH19 : forall (j_6: Z) , (((y <= j_6) /\ (j_6 < ((n_pre + 1 ) * W ))) -> ((Znth (j_6) (kl_2) (0)) = 0))) (PreH20 : forall (j_7: Z) , (((0 <= j_7) /\ (j_7 < ((n_pre + 1 ) * W ))) -> ((Znth (j_7) (dl_2) (0)) = 0))) ,
  (Int64Array.full fac (N + 1 ) fl_2 )
  **  (Int64Array.full ifac (N + 1 ) il_2 )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl_2 )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl_2 )
|--
  EX (dl: (@list Z))  (kl: (@list Z))  (il: (@list Z))  (fl: (@list Z)) ,
  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre 1 0 kl dl ) ”
  &&  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
) \/
(
forall (m_pre: Z) (n_pre: Z) (y: Z) (dl_2: (@list Z)) (kl_2: (@list Z)) (il_2: (@list Z)) (fl_2: (@list Z)) (W: Z) (N: Z) (PreH1 : (y > m_pre)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (W = (m_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 2000)) (PreH8 : ((Zlength (fl_2)) = (N + 1 ))) (PreH9 : ((Zlength (il_2)) = (N + 1 ))) (PreH10 : ((Zlength (kl_2)) = ((n_pre + 1 ) * W ))) (PreH11 : ((Zlength (dl_2)) = ((n_pre + 1 ) * W ))) (PreH12 : (P080Factorials fl_2 (N + 1 ) )) (PreH13 : (P080InverseFactorials il_2 0 (N + 1 ) )) (PreH14 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (N + 1 ))) -> ((((0 <= (Znth (j_3) (fl_2) (0))) /\ ((Znth (j_3) (fl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_3) (il_2) (0)))) /\ ((Znth (j_3) (il_2) (0)) < 998244853)))) (PreH15 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_4) (kl_2) (0))) /\ ((Znth (j_4) (kl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_4) (dl_2) (0)))) /\ ((Znth (j_4) (dl_2) (0)) < 998244853)))) (PreH16 : (0 <= y)) (PreH17 : (y <= (m_pre + 1 ))) (PreH18 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < y)) -> ((Znth (j_5) (kl_2) (0)) = 1))) (PreH19 : forall (j_6: Z) , (((y <= j_6) /\ (j_6 < ((n_pre + 1 ) * W ))) -> ((Znth (j_6) (kl_2) (0)) = 0))) (PreH20 : forall (j_7: Z) , (((0 <= j_7) /\ (j_7 < ((n_pre + 1 ) * W ))) -> ((Znth (j_7) (dl_2) (0)) = 0))) ,
  TT && emp 
|--
  “ (P080Tables n_pre m_pre 1 0 kl_2 dl_2 ) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl_2) (0))) /\ ((Znth (j_2) (kl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl_2) (0)))) /\ ((Znth (j_2) (dl_2) (0)) < 998244853))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl_2) (0))) /\ ((Znth (j) (fl_2) (0)) < 998244853)) /\ (0 <= (Znth (j) (il_2) (0)))) /\ ((Znth (j) (il_2) (0)) < 998244853))) ”
  &&  emp
).

Definition solver_entail_wit_7_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (y: Z) (dl_2: (@list Z)) (kl_2: (@list Z)) (il_2: (@list Z)) (fl_2: (@list Z)) (W: Z) (N: Z) (PreH1 : (y > m_pre)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (W = (m_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 2000)) (PreH8 : ((Zlength (fl_2)) = (N + 1 ))) (PreH9 : ((Zlength (il_2)) = (N + 1 ))) (PreH10 : ((Zlength (kl_2)) = ((n_pre + 1 ) * W ))) (PreH11 : ((Zlength (dl_2)) = ((n_pre + 1 ) * W ))) (PreH12 : (P080Factorials fl_2 (N + 1 ) )) (PreH13 : (P080InverseFactorials il_2 0 (N + 1 ) )) (PreH14 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (N + 1 ))) -> ((((0 <= (Znth (j_3) (fl_2) (0))) /\ ((Znth (j_3) (fl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_3) (il_2) (0)))) /\ ((Znth (j_3) (il_2) (0)) < 998244853)))) (PreH15 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_4) (kl_2) (0))) /\ ((Znth (j_4) (kl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_4) (dl_2) (0)))) /\ ((Znth (j_4) (dl_2) (0)) < 998244853)))) (PreH16 : (0 <= y)) (PreH17 : (y <= (m_pre + 1 ))) (PreH18 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < y)) -> ((Znth (j_5) (kl_2) (0)) = 1))) (PreH19 : forall (j_6: Z) , (((y <= j_6) /\ (j_6 < ((n_pre + 1 ) * W ))) -> ((Znth (j_6) (kl_2) (0)) = 0))) (PreH20 : forall (j_7: Z) , (((0 <= j_7) /\ (j_7 < ((n_pre + 1 ) * W ))) -> ((Znth (j_7) (dl_2) (0)) = 0))) ,
  (P080Tables n_pre m_pre 1 0 kl_2 dl_2 )
.

Definition solver_entail_wit_7_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (y: Z) (dl_2: (@list Z)) (kl_2: (@list Z)) (il_2: (@list Z)) (fl_2: (@list Z)) (W: Z) (N: Z) (PreH1 : (y > m_pre)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (W = (m_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 2000)) (PreH8 : ((Zlength (fl_2)) = (N + 1 ))) (PreH9 : ((Zlength (il_2)) = (N + 1 ))) (PreH10 : ((Zlength (kl_2)) = ((n_pre + 1 ) * W ))) (PreH11 : ((Zlength (dl_2)) = ((n_pre + 1 ) * W ))) (PreH12 : (P080Factorials fl_2 (N + 1 ) )) (PreH13 : (P080InverseFactorials il_2 0 (N + 1 ) )) (PreH14 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (N + 1 ))) -> ((((0 <= (Znth (j_3) (fl_2) (0))) /\ ((Znth (j_3) (fl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_3) (il_2) (0)))) /\ ((Znth (j_3) (il_2) (0)) < 998244853)))) (PreH15 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_4) (kl_2) (0))) /\ ((Znth (j_4) (kl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_4) (dl_2) (0)))) /\ ((Znth (j_4) (dl_2) (0)) < 998244853)))) (PreH16 : (0 <= y)) (PreH17 : (y <= (m_pre + 1 ))) (PreH18 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < y)) -> ((Znth (j_5) (kl_2) (0)) = 1))) (PreH19 : forall (j_6: Z) , (((y <= j_6) /\ (j_6 < ((n_pre + 1 ) * W ))) -> ((Znth (j_6) (kl_2) (0)) = 0))) (PreH20 : forall (j_7: Z) , (((0 <= j_7) /\ (j_7 < ((n_pre + 1 ) * W ))) -> ((Znth (j_7) (dl_2) (0)) = 0))) ,
  forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl_2) (0))) /\ ((Znth (j_2) (kl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl_2) (0)))) /\ ((Znth (j_2) (dl_2) (0)) < 998244853)))
.

Definition solver_entail_wit_7_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (y: Z) (dl_2: (@list Z)) (kl_2: (@list Z)) (il_2: (@list Z)) (fl_2: (@list Z)) (W: Z) (N: Z) (PreH1 : (y > m_pre)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (W = (m_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 2000)) (PreH8 : ((Zlength (fl_2)) = (N + 1 ))) (PreH9 : ((Zlength (il_2)) = (N + 1 ))) (PreH10 : ((Zlength (kl_2)) = ((n_pre + 1 ) * W ))) (PreH11 : ((Zlength (dl_2)) = ((n_pre + 1 ) * W ))) (PreH12 : (P080Factorials fl_2 (N + 1 ) )) (PreH13 : (P080InverseFactorials il_2 0 (N + 1 ) )) (PreH14 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (N + 1 ))) -> ((((0 <= (Znth (j_3) (fl_2) (0))) /\ ((Znth (j_3) (fl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_3) (il_2) (0)))) /\ ((Znth (j_3) (il_2) (0)) < 998244853)))) (PreH15 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_4) (kl_2) (0))) /\ ((Znth (j_4) (kl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_4) (dl_2) (0)))) /\ ((Znth (j_4) (dl_2) (0)) < 998244853)))) (PreH16 : (0 <= y)) (PreH17 : (y <= (m_pre + 1 ))) (PreH18 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < y)) -> ((Znth (j_5) (kl_2) (0)) = 1))) (PreH19 : forall (j_6: Z) , (((y <= j_6) /\ (j_6 < ((n_pre + 1 ) * W ))) -> ((Znth (j_6) (kl_2) (0)) = 0))) (PreH20 : forall (j_7: Z) , (((0 <= j_7) /\ (j_7 < ((n_pre + 1 ) * W ))) -> ((Znth (j_7) (dl_2) (0)) = 0))) ,
  forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl_2) (0))) /\ ((Znth (j) (fl_2) (0)) < 998244853)) /\ (0 <= (Znth (j) (il_2) (0)))) /\ ((Znth (j) (il_2) (0)) < 998244853)))
.

Definition solver_entail_wit_8 := 
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= n_pre)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (W = (m_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 2000)) (PreH8 : ((Zlength (fl)) = (N + 1 ))) (PreH9 : ((Zlength (il)) = (N + 1 ))) (PreH10 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH11 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH12 : (P080Factorials fl (N + 1 ) )) (PreH13 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH16 : (1 <= x)) (PreH17 : (x <= (n_pre + 1 ))) (PreH18 : (P080Tables n_pre m_pre x 0 kl dl )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (0 <= (x * W )) ” 
  &&  “ ((x * W ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (N >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= (n_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre x 0 kl dl ) ”
  &&  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
) \/
(
forall (m_pre: Z) (n_pre: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= INT_MAX)) (PreH2 : (W <= INT_MAX)) (PreH3 : (N <= INT_MAX)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (x >= INT_MIN)) (PreH7 : (W >= INT_MIN)) (PreH8 : (N >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (x <= n_pre)) (PreH12 : (N = (n_pre + m_pre ))) (PreH13 : (W = (m_pre + 1 ))) (PreH14 : (0 <= n_pre)) (PreH15 : (n_pre <= 2000)) (PreH16 : (0 <= m_pre)) (PreH17 : (m_pre <= 2000)) (PreH18 : ((Zlength (fl)) = (N + 1 ))) (PreH19 : ((Zlength (il)) = (N + 1 ))) (PreH20 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH21 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH22 : (P080Factorials fl (N + 1 ) )) (PreH23 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH24 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH25 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH26 : (1 <= x)) (PreH27 : (x <= (n_pre + 1 ))) (PreH28 : (P080Tables n_pre m_pre x 0 kl dl )) ,
  TT && emp 
|--
  “ ((x * (m_pre + 1 ) ) < ((n_pre + 1 ) * (m_pre + 1 ) )) ”
  &&  emp
).

Definition solver_entail_wit_8_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= INT_MAX)) (PreH2 : (W <= INT_MAX)) (PreH3 : (N <= INT_MAX)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (x >= INT_MIN)) (PreH7 : (W >= INT_MIN)) (PreH8 : (N >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (x <= n_pre)) (PreH12 : (N = (n_pre + m_pre ))) (PreH13 : (W = (m_pre + 1 ))) (PreH14 : (0 <= n_pre)) (PreH15 : (n_pre <= 2000)) (PreH16 : (0 <= m_pre)) (PreH17 : (m_pre <= 2000)) (PreH18 : ((Zlength (fl)) = (N + 1 ))) (PreH19 : ((Zlength (il)) = (N + 1 ))) (PreH20 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH21 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH22 : (P080Factorials fl (N + 1 ) )) (PreH23 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH24 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH25 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH26 : (1 <= x)) (PreH27 : (x <= (n_pre + 1 ))) (PreH28 : (P080Tables n_pre m_pre x 0 kl dl )) ,
  ((x * (m_pre + 1 ) ) < ((n_pre + 1 ) * (m_pre + 1 ) ))
.

Definition solver_entail_wit_9 := 
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (x: Z) (dl_2: (@list Z)) (kl_2: (@list Z)) (il_2: (@list Z)) (fl_2: (@list Z)) (W: Z) (N: Z) (PreH1 : (0 <= (x * W ))) (PreH2 : ((x * W ) < ((n_pre + 1 ) * W ))) (PreH3 : (N <= INT_MAX)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (N >= INT_MIN)) (PreH6 : (m_pre >= INT_MIN)) (PreH7 : (x <= n_pre)) (PreH8 : (N = (n_pre + m_pre ))) (PreH9 : (W = (m_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 2000)) (PreH12 : (0 <= m_pre)) (PreH13 : (m_pre <= 2000)) (PreH14 : ((Zlength (fl_2)) = (N + 1 ))) (PreH15 : ((Zlength (il_2)) = (N + 1 ))) (PreH16 : ((Zlength (kl_2)) = ((n_pre + 1 ) * W ))) (PreH17 : ((Zlength (dl_2)) = ((n_pre + 1 ) * W ))) (PreH18 : (P080Factorials fl_2 (N + 1 ) )) (PreH19 : (P080InverseFactorials il_2 0 (N + 1 ) )) (PreH20 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (N + 1 ))) -> ((((0 <= (Znth (j_3) (fl_2) (0))) /\ ((Znth (j_3) (fl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_3) (il_2) (0)))) /\ ((Znth (j_3) (il_2) (0)) < 998244853)))) (PreH21 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_4) (kl_2) (0))) /\ ((Znth (j_4) (kl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_4) (dl_2) (0)))) /\ ((Znth (j_4) (dl_2) (0)) < 998244853)))) (PreH22 : (1 <= x)) (PreH23 : (x <= (n_pre + 1 ))) (PreH24 : (P080Tables n_pre m_pre x 0 kl_2 dl_2 )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + 0 )) (x) (dl_2)) )
  **  (Int64Array.full fac (N + 1 ) fl_2 )
  **  (Int64Array.full ifac (N + 1 ) il_2 )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl_2 )
|--
  EX (dl: (@list Z))  (kl: (@list Z))  (il: (@list Z))  (fl: (@list Z)) ,
  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (m_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre x 1 kl dl ) ”
  &&  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
) \/
(
forall (m_pre: Z) (n_pre: Z) (x: Z) (dl_2: (@list Z)) (kl_2: (@list Z)) (il_2: (@list Z)) (fl_2: (@list Z)) (W: Z) (N: Z) (PreH1 : (0 <= (x * W ))) (PreH2 : ((x * W ) < ((n_pre + 1 ) * W ))) (PreH3 : (N <= INT_MAX)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (N >= INT_MIN)) (PreH6 : (m_pre >= INT_MIN)) (PreH7 : (x <= n_pre)) (PreH8 : (N = (n_pre + m_pre ))) (PreH9 : (W = (m_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 2000)) (PreH12 : (0 <= m_pre)) (PreH13 : (m_pre <= 2000)) (PreH14 : ((Zlength (fl_2)) = (N + 1 ))) (PreH15 : ((Zlength (il_2)) = (N + 1 ))) (PreH16 : ((Zlength (kl_2)) = ((n_pre + 1 ) * W ))) (PreH17 : ((Zlength (dl_2)) = ((n_pre + 1 ) * W ))) (PreH18 : (P080Factorials fl_2 (N + 1 ) )) (PreH19 : (P080InverseFactorials il_2 0 (N + 1 ) )) (PreH20 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (N + 1 ))) -> ((((0 <= (Znth (j_3) (fl_2) (0))) /\ ((Znth (j_3) (fl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_3) (il_2) (0)))) /\ ((Znth (j_3) (il_2) (0)) < 998244853)))) (PreH21 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_4) (kl_2) (0))) /\ ((Znth (j_4) (kl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_4) (dl_2) (0)))) /\ ((Znth (j_4) (dl_2) (0)) < 998244853)))) (PreH22 : (1 <= x)) (PreH23 : (x <= (n_pre + 1 ))) (PreH24 : (P080Tables n_pre m_pre x 0 kl_2 dl_2 )) ,
  TT && emp 
|--
  “ (P080Tables n_pre m_pre x 1 kl_2 (replace_Znth (((x * (m_pre + 1 ) ) + 0 )) (x) (dl_2)) ) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl_2) (0))) /\ ((Znth (j_2) (kl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_2) ((replace_Znth (((x * W ) + 0 )) (x) (dl_2))) (0)))) /\ ((Znth (j_2) ((replace_Znth (((x * W ) + 0 )) (x) (dl_2))) (0)) < 998244853))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl_2) (0))) /\ ((Znth (j) (fl_2) (0)) < 998244853)) /\ (0 <= (Znth (j) (il_2) (0)))) /\ ((Znth (j) (il_2) (0)) < 998244853))) ” 
  &&  “ ((Zlength ((replace_Znth (((x * (m_pre + 1 ) ) + 0 )) (x) (dl_2)))) = ((n_pre + 1 ) * (m_pre + 1 ) )) ”
  &&  emp
).

Definition solver_entail_wit_9_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (x: Z) (dl_2: (@list Z)) (kl_2: (@list Z)) (il_2: (@list Z)) (fl_2: (@list Z)) (W: Z) (N: Z) (PreH1 : (0 <= (x * W ))) (PreH2 : ((x * W ) < ((n_pre + 1 ) * W ))) (PreH3 : (N <= INT_MAX)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (N >= INT_MIN)) (PreH6 : (m_pre >= INT_MIN)) (PreH7 : (x <= n_pre)) (PreH8 : (N = (n_pre + m_pre ))) (PreH9 : (W = (m_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 2000)) (PreH12 : (0 <= m_pre)) (PreH13 : (m_pre <= 2000)) (PreH14 : ((Zlength (fl_2)) = (N + 1 ))) (PreH15 : ((Zlength (il_2)) = (N + 1 ))) (PreH16 : ((Zlength (kl_2)) = ((n_pre + 1 ) * W ))) (PreH17 : ((Zlength (dl_2)) = ((n_pre + 1 ) * W ))) (PreH18 : (P080Factorials fl_2 (N + 1 ) )) (PreH19 : (P080InverseFactorials il_2 0 (N + 1 ) )) (PreH20 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (N + 1 ))) -> ((((0 <= (Znth (j_3) (fl_2) (0))) /\ ((Znth (j_3) (fl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_3) (il_2) (0)))) /\ ((Znth (j_3) (il_2) (0)) < 998244853)))) (PreH21 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_4) (kl_2) (0))) /\ ((Znth (j_4) (kl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_4) (dl_2) (0)))) /\ ((Znth (j_4) (dl_2) (0)) < 998244853)))) (PreH22 : (1 <= x)) (PreH23 : (x <= (n_pre + 1 ))) (PreH24 : (P080Tables n_pre m_pre x 0 kl_2 dl_2 )) ,
  (P080Tables n_pre m_pre x 1 kl_2 (replace_Znth (((x * (m_pre + 1 ) ) + 0 )) (x) (dl_2)) )
.

Definition solver_entail_wit_9_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (x: Z) (dl_2: (@list Z)) (kl_2: (@list Z)) (il_2: (@list Z)) (fl_2: (@list Z)) (W: Z) (N: Z) (PreH1 : (0 <= (x * W ))) (PreH2 : ((x * W ) < ((n_pre + 1 ) * W ))) (PreH3 : (N <= INT_MAX)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (N >= INT_MIN)) (PreH6 : (m_pre >= INT_MIN)) (PreH7 : (x <= n_pre)) (PreH8 : (N = (n_pre + m_pre ))) (PreH9 : (W = (m_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 2000)) (PreH12 : (0 <= m_pre)) (PreH13 : (m_pre <= 2000)) (PreH14 : ((Zlength (fl_2)) = (N + 1 ))) (PreH15 : ((Zlength (il_2)) = (N + 1 ))) (PreH16 : ((Zlength (kl_2)) = ((n_pre + 1 ) * W ))) (PreH17 : ((Zlength (dl_2)) = ((n_pre + 1 ) * W ))) (PreH18 : (P080Factorials fl_2 (N + 1 ) )) (PreH19 : (P080InverseFactorials il_2 0 (N + 1 ) )) (PreH20 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (N + 1 ))) -> ((((0 <= (Znth (j_3) (fl_2) (0))) /\ ((Znth (j_3) (fl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_3) (il_2) (0)))) /\ ((Znth (j_3) (il_2) (0)) < 998244853)))) (PreH21 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_4) (kl_2) (0))) /\ ((Znth (j_4) (kl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_4) (dl_2) (0)))) /\ ((Znth (j_4) (dl_2) (0)) < 998244853)))) (PreH22 : (1 <= x)) (PreH23 : (x <= (n_pre + 1 ))) (PreH24 : (P080Tables n_pre m_pre x 0 kl_2 dl_2 )) ,
  forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl_2) (0))) /\ ((Znth (j_2) (kl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_2) ((replace_Znth (((x * W ) + 0 )) (x) (dl_2))) (0)))) /\ ((Znth (j_2) ((replace_Znth (((x * W ) + 0 )) (x) (dl_2))) (0)) < 998244853)))
.

Definition solver_entail_wit_9_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (x: Z) (dl_2: (@list Z)) (kl_2: (@list Z)) (il_2: (@list Z)) (fl_2: (@list Z)) (W: Z) (N: Z) (PreH1 : (0 <= (x * W ))) (PreH2 : ((x * W ) < ((n_pre + 1 ) * W ))) (PreH3 : (N <= INT_MAX)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (N >= INT_MIN)) (PreH6 : (m_pre >= INT_MIN)) (PreH7 : (x <= n_pre)) (PreH8 : (N = (n_pre + m_pre ))) (PreH9 : (W = (m_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 2000)) (PreH12 : (0 <= m_pre)) (PreH13 : (m_pre <= 2000)) (PreH14 : ((Zlength (fl_2)) = (N + 1 ))) (PreH15 : ((Zlength (il_2)) = (N + 1 ))) (PreH16 : ((Zlength (kl_2)) = ((n_pre + 1 ) * W ))) (PreH17 : ((Zlength (dl_2)) = ((n_pre + 1 ) * W ))) (PreH18 : (P080Factorials fl_2 (N + 1 ) )) (PreH19 : (P080InverseFactorials il_2 0 (N + 1 ) )) (PreH20 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (N + 1 ))) -> ((((0 <= (Znth (j_3) (fl_2) (0))) /\ ((Znth (j_3) (fl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_3) (il_2) (0)))) /\ ((Znth (j_3) (il_2) (0)) < 998244853)))) (PreH21 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_4) (kl_2) (0))) /\ ((Znth (j_4) (kl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_4) (dl_2) (0)))) /\ ((Znth (j_4) (dl_2) (0)) < 998244853)))) (PreH22 : (1 <= x)) (PreH23 : (x <= (n_pre + 1 ))) (PreH24 : (P080Tables n_pre m_pre x 0 kl_2 dl_2 )) ,
  forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl_2) (0))) /\ ((Znth (j) (fl_2) (0)) < 998244853)) /\ (0 <= (Znth (j) (il_2) (0)))) /\ ((Znth (j) (il_2) (0)) < 998244853)))
.

Definition solver_entail_wit_9_split_goal_4 := 
forall (m_pre: Z) (n_pre: Z) (x: Z) (dl_2: (@list Z)) (kl_2: (@list Z)) (il_2: (@list Z)) (fl_2: (@list Z)) (W: Z) (N: Z) (PreH1 : (0 <= (x * W ))) (PreH2 : ((x * W ) < ((n_pre + 1 ) * W ))) (PreH3 : (N <= INT_MAX)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (N >= INT_MIN)) (PreH6 : (m_pre >= INT_MIN)) (PreH7 : (x <= n_pre)) (PreH8 : (N = (n_pre + m_pre ))) (PreH9 : (W = (m_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 2000)) (PreH12 : (0 <= m_pre)) (PreH13 : (m_pre <= 2000)) (PreH14 : ((Zlength (fl_2)) = (N + 1 ))) (PreH15 : ((Zlength (il_2)) = (N + 1 ))) (PreH16 : ((Zlength (kl_2)) = ((n_pre + 1 ) * W ))) (PreH17 : ((Zlength (dl_2)) = ((n_pre + 1 ) * W ))) (PreH18 : (P080Factorials fl_2 (N + 1 ) )) (PreH19 : (P080InverseFactorials il_2 0 (N + 1 ) )) (PreH20 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (N + 1 ))) -> ((((0 <= (Znth (j_3) (fl_2) (0))) /\ ((Znth (j_3) (fl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_3) (il_2) (0)))) /\ ((Znth (j_3) (il_2) (0)) < 998244853)))) (PreH21 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_4) (kl_2) (0))) /\ ((Znth (j_4) (kl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_4) (dl_2) (0)))) /\ ((Znth (j_4) (dl_2) (0)) < 998244853)))) (PreH22 : (1 <= x)) (PreH23 : (x <= (n_pre + 1 ))) (PreH24 : (P080Tables n_pre m_pre x 0 kl_2 dl_2 )) ,
  ((Zlength ((replace_Znth (((x * (m_pre + 1 ) ) + 0 )) (x) (dl_2)))) = ((n_pre + 1 ) * (m_pre + 1 ) ))
.

Definition solver_entail_wit_10 := 
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= m_pre)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (W = (m_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 2000)) (PreH8 : ((Zlength (fl)) = (N + 1 ))) (PreH9 : ((Zlength (il)) = (N + 1 ))) (PreH10 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH11 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH12 : (P080Factorials fl (N + 1 ) )) (PreH13 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH16 : (1 <= x)) (PreH17 : (x <= n_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= (m_pre + 1 ))) (PreH20 : (P080Tables n_pre m_pre x y kl dl )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (0 <= ((x * W ) + y )) ” 
  &&  “ (((x * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= (((x - 1 ) * W ) + y )) ” 
  &&  “ ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= ((x * W ) + (y - 1 ) )) ” 
  &&  “ (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (N >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (y <= m_pre) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (1 <= y) ” 
  &&  “ (y <= (m_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre x y kl dl ) ”
  &&  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "y" ) )) # Int  |-> y)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
) \/
(
forall (m_pre: Z) (n_pre: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= INT_MAX)) (PreH2 : (x <= INT_MAX)) (PreH3 : (W <= INT_MAX)) (PreH4 : (N <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (y >= INT_MIN)) (PreH8 : (x >= INT_MIN)) (PreH9 : (W >= INT_MIN)) (PreH10 : (N >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (y <= m_pre)) (PreH14 : (N = (n_pre + m_pre ))) (PreH15 : (W = (m_pre + 1 ))) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 2000)) (PreH18 : (0 <= m_pre)) (PreH19 : (m_pre <= 2000)) (PreH20 : ((Zlength (fl)) = (N + 1 ))) (PreH21 : ((Zlength (il)) = (N + 1 ))) (PreH22 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH23 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH24 : (P080Factorials fl (N + 1 ) )) (PreH25 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH26 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH27 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH28 : (1 <= x)) (PreH29 : (x <= n_pre)) (PreH30 : (1 <= y)) (PreH31 : (y <= (m_pre + 1 ))) (PreH32 : (P080Tables n_pre m_pre x y kl dl )) ,
  TT && emp 
|--
  “ (((x * (m_pre + 1 ) ) + (y - 1 ) ) < ((n_pre + 1 ) * (m_pre + 1 ) )) ” 
  &&  “ ((((x - 1 ) * (m_pre + 1 ) ) + y ) < ((n_pre + 1 ) * (m_pre + 1 ) )) ” 
  &&  “ (((x * (m_pre + 1 ) ) + y ) < ((n_pre + 1 ) * (m_pre + 1 ) )) ”
  &&  emp
).

Definition solver_entail_wit_10_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= INT_MAX)) (PreH2 : (x <= INT_MAX)) (PreH3 : (W <= INT_MAX)) (PreH4 : (N <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (y >= INT_MIN)) (PreH8 : (x >= INT_MIN)) (PreH9 : (W >= INT_MIN)) (PreH10 : (N >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (y <= m_pre)) (PreH14 : (N = (n_pre + m_pre ))) (PreH15 : (W = (m_pre + 1 ))) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 2000)) (PreH18 : (0 <= m_pre)) (PreH19 : (m_pre <= 2000)) (PreH20 : ((Zlength (fl)) = (N + 1 ))) (PreH21 : ((Zlength (il)) = (N + 1 ))) (PreH22 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH23 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH24 : (P080Factorials fl (N + 1 ) )) (PreH25 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH26 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH27 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH28 : (1 <= x)) (PreH29 : (x <= n_pre)) (PreH30 : (1 <= y)) (PreH31 : (y <= (m_pre + 1 ))) (PreH32 : (P080Tables n_pre m_pre x y kl dl )) ,
  (((x * (m_pre + 1 ) ) + (y - 1 ) ) < ((n_pre + 1 ) * (m_pre + 1 ) ))
.

Definition solver_entail_wit_10_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= INT_MAX)) (PreH2 : (x <= INT_MAX)) (PreH3 : (W <= INT_MAX)) (PreH4 : (N <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (y >= INT_MIN)) (PreH8 : (x >= INT_MIN)) (PreH9 : (W >= INT_MIN)) (PreH10 : (N >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (y <= m_pre)) (PreH14 : (N = (n_pre + m_pre ))) (PreH15 : (W = (m_pre + 1 ))) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 2000)) (PreH18 : (0 <= m_pre)) (PreH19 : (m_pre <= 2000)) (PreH20 : ((Zlength (fl)) = (N + 1 ))) (PreH21 : ((Zlength (il)) = (N + 1 ))) (PreH22 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH23 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH24 : (P080Factorials fl (N + 1 ) )) (PreH25 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH26 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH27 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH28 : (1 <= x)) (PreH29 : (x <= n_pre)) (PreH30 : (1 <= y)) (PreH31 : (y <= (m_pre + 1 ))) (PreH32 : (P080Tables n_pre m_pre x y kl dl )) ,
  ((((x - 1 ) * (m_pre + 1 ) ) + y ) < ((n_pre + 1 ) * (m_pre + 1 ) ))
.

Definition solver_entail_wit_10_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= INT_MAX)) (PreH2 : (x <= INT_MAX)) (PreH3 : (W <= INT_MAX)) (PreH4 : (N <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (y >= INT_MIN)) (PreH8 : (x >= INT_MIN)) (PreH9 : (W >= INT_MIN)) (PreH10 : (N >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (y <= m_pre)) (PreH14 : (N = (n_pre + m_pre ))) (PreH15 : (W = (m_pre + 1 ))) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 2000)) (PreH18 : (0 <= m_pre)) (PreH19 : (m_pre <= 2000)) (PreH20 : ((Zlength (fl)) = (N + 1 ))) (PreH21 : ((Zlength (il)) = (N + 1 ))) (PreH22 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH23 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH24 : (P080Factorials fl (N + 1 ) )) (PreH25 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH26 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH27 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH28 : (1 <= x)) (PreH29 : (x <= n_pre)) (PreH30 : (1 <= y)) (PreH31 : (y <= (m_pre + 1 ))) (PreH32 : (P080Tables n_pre m_pre x y kl dl )) ,
  (((x * (m_pre + 1 ) ) + y ) < ((n_pre + 1 ) * (m_pre + 1 ) ))
.

Definition solver_entail_wit_11_1 := 
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl_2: (@list Z)) (kl_2: (@list Z)) (il_2: (@list Z)) (fl_2: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl_2)) = (N + 1 ))) (PreH24 : ((Zlength (il_2)) = (N + 1 ))) (PreH25 : ((Zlength (kl_2)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl_2)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl_2 (N + 1 ) )) (PreH28 : (P080InverseFactorials il_2 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl_2) (0))) /\ ((Znth (j) (fl_2) (0)) < 998244853)) /\ (0 <= (Znth (j) (il_2) (0)))) /\ ((Znth (j) (il_2) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl_2) (0))) /\ ((Znth (j_2) (kl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl_2) (0)))) /\ ((Znth (j_2) (dl_2) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl_2 dl_2 )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) (((((((((((((Znth ((x + y ) - 1 ) fl_2 0) * (Znth y il_2 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il_2 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl_2 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl_2 0) ) - (((((Znth ((x + y ) - 1 ) fl_2 0) * (Znth x il_2 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il_2 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl_2 0) + (Znth ((x * W ) + (y - 1 ) ) kl_2 0) ) % ( 998244853 ) )) (kl_2)) 0) ) % ( 998244853 ) ) + 998244853 ) % ( 998244853 ) )) (dl_2)) )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl_2 0) + (Znth ((x * W ) + (y - 1 ) ) kl_2 0) ) % ( 998244853 ) )) (kl_2)) )
  **  (Int64Array.full ifac (N + 1 ) il_2 )
  **  (Int64Array.full fac (N + 1 ) fl_2 )
|--
  EX (dl: (@list Z))  (kl: (@list Z))  (il: (@list Z))  (fl: (@list Z)) ,
  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (1 <= (y + 1 )) ” 
  &&  “ ((y + 1 ) <= (m_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre x (y + 1 ) kl dl ) ”
  &&  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
) \/
(
forall (m_pre: Z) (n_pre: Z) (y: Z) (x: Z) (dl_2: (@list Z)) (kl_2: (@list Z)) (il_2: (@list Z)) (fl_2: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl_2)) = (N + 1 ))) (PreH24 : ((Zlength (il_2)) = (N + 1 ))) (PreH25 : ((Zlength (kl_2)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl_2)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl_2 (N + 1 ) )) (PreH28 : (P080InverseFactorials il_2 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl_2) (0))) /\ ((Znth (j) (fl_2) (0)) < 998244853)) /\ (0 <= (Znth (j) (il_2) (0)))) /\ ((Znth (j) (il_2) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl_2) (0))) /\ ((Znth (j_2) (kl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl_2) (0)))) /\ ((Znth (j_2) (dl_2) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl_2 dl_2 )) ,
  TT && emp 
|--
  “ (P080Tables n_pre m_pre x (y + 1 ) (replace_Znth (((x * (m_pre + 1 ) ) + y )) ((((Znth (((x - 1 ) * (m_pre + 1 ) ) + y ) kl_2 0) + (Znth ((x * (m_pre + 1 ) ) + (y - 1 ) ) kl_2 0) ) % ( 998244853 ) )) (kl_2)) (replace_Znth (((x * (m_pre + 1 ) ) + y )) (((((((((((((Znth ((x + y ) - 1 ) fl_2 0) * (Znth y il_2 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il_2 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * (m_pre + 1 ) ) + y ) dl_2 0) ) + (Znth ((x * (m_pre + 1 ) ) + (y - 1 ) ) dl_2 0) ) - (((((Znth ((x + y ) - 1 ) fl_2 0) * (Znth x il_2 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il_2 0) ) % ( 998244853 ) ) ) + (Znth ((x * (m_pre + 1 ) ) + (y - 1 ) ) (replace_Znth (((x * (m_pre + 1 ) ) + y )) ((((Znth (((x - 1 ) * (m_pre + 1 ) ) + y ) kl_2 0) + (Znth ((x * (m_pre + 1 ) ) + (y - 1 ) ) kl_2 0) ) % ( 998244853 ) )) (kl_2)) 0) ) % ( 998244853 ) ) + 998244853 ) % ( 998244853 ) )) (dl_2)) ) ” 
  &&  “ ((Zlength ((replace_Znth (((x * (m_pre + 1 ) ) + y )) (((((((((((((Znth ((x + y ) - 1 ) fl_2 0) * (Znth y il_2 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il_2 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * (m_pre + 1 ) ) + y ) dl_2 0) ) + (Znth ((x * (m_pre + 1 ) ) + (y - 1 ) ) dl_2 0) ) - (((((Znth ((x + y ) - 1 ) fl_2 0) * (Znth x il_2 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il_2 0) ) % ( 998244853 ) ) ) + (Znth ((x * (m_pre + 1 ) ) + (y - 1 ) ) (replace_Znth (((x * (m_pre + 1 ) ) + y )) ((((Znth (((x - 1 ) * (m_pre + 1 ) ) + y ) kl_2 0) + (Znth ((x * (m_pre + 1 ) ) + (y - 1 ) ) kl_2 0) ) % ( 998244853 ) )) (kl_2)) 0) ) % ( 998244853 ) ) + 998244853 ) % ( 998244853 ) )) (dl_2)))) = ((n_pre + 1 ) * (m_pre + 1 ) )) ” 
  &&  “ ((Zlength ((replace_Znth (((x * (m_pre + 1 ) ) + y )) ((((Znth (((x - 1 ) * (m_pre + 1 ) ) + y ) kl_2 0) + (Znth ((x * (m_pre + 1 ) ) + (y - 1 ) ) kl_2 0) ) % ( 998244853 ) )) (kl_2)))) = ((n_pre + 1 ) * (m_pre + 1 ) )) ”
  &&  emp
).

Definition solver_entail_wit_11_1_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (y: Z) (x: Z) (dl_2: (@list Z)) (kl_2: (@list Z)) (il_2: (@list Z)) (fl_2: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl_2)) = (N + 1 ))) (PreH24 : ((Zlength (il_2)) = (N + 1 ))) (PreH25 : ((Zlength (kl_2)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl_2)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl_2 (N + 1 ) )) (PreH28 : (P080InverseFactorials il_2 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl_2) (0))) /\ ((Znth (j) (fl_2) (0)) < 998244853)) /\ (0 <= (Znth (j) (il_2) (0)))) /\ ((Znth (j) (il_2) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl_2) (0))) /\ ((Znth (j_2) (kl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl_2) (0)))) /\ ((Znth (j_2) (dl_2) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl_2 dl_2 )) ,
  (P080Tables n_pre m_pre x (y + 1 ) (replace_Znth (((x * (m_pre + 1 ) ) + y )) ((((Znth (((x - 1 ) * (m_pre + 1 ) ) + y ) kl_2 0) + (Znth ((x * (m_pre + 1 ) ) + (y - 1 ) ) kl_2 0) ) % ( 998244853 ) )) (kl_2)) (replace_Znth (((x * (m_pre + 1 ) ) + y )) (((((((((((((Znth ((x + y ) - 1 ) fl_2 0) * (Znth y il_2 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il_2 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * (m_pre + 1 ) ) + y ) dl_2 0) ) + (Znth ((x * (m_pre + 1 ) ) + (y - 1 ) ) dl_2 0) ) - (((((Znth ((x + y ) - 1 ) fl_2 0) * (Znth x il_2 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il_2 0) ) % ( 998244853 ) ) ) + (Znth ((x * (m_pre + 1 ) ) + (y - 1 ) ) (replace_Znth (((x * (m_pre + 1 ) ) + y )) ((((Znth (((x - 1 ) * (m_pre + 1 ) ) + y ) kl_2 0) + (Znth ((x * (m_pre + 1 ) ) + (y - 1 ) ) kl_2 0) ) % ( 998244853 ) )) (kl_2)) 0) ) % ( 998244853 ) ) + 998244853 ) % ( 998244853 ) )) (dl_2)) )
.

Definition solver_entail_wit_11_1_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (y: Z) (x: Z) (dl_2: (@list Z)) (kl_2: (@list Z)) (il_2: (@list Z)) (fl_2: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl_2)) = (N + 1 ))) (PreH24 : ((Zlength (il_2)) = (N + 1 ))) (PreH25 : ((Zlength (kl_2)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl_2)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl_2 (N + 1 ) )) (PreH28 : (P080InverseFactorials il_2 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl_2) (0))) /\ ((Znth (j) (fl_2) (0)) < 998244853)) /\ (0 <= (Znth (j) (il_2) (0)))) /\ ((Znth (j) (il_2) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl_2) (0))) /\ ((Znth (j_2) (kl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl_2) (0)))) /\ ((Znth (j_2) (dl_2) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl_2 dl_2 )) ,
  ((Zlength ((replace_Znth (((x * (m_pre + 1 ) ) + y )) (((((((((((((Znth ((x + y ) - 1 ) fl_2 0) * (Znth y il_2 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il_2 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * (m_pre + 1 ) ) + y ) dl_2 0) ) + (Znth ((x * (m_pre + 1 ) ) + (y - 1 ) ) dl_2 0) ) - (((((Znth ((x + y ) - 1 ) fl_2 0) * (Znth x il_2 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il_2 0) ) % ( 998244853 ) ) ) + (Znth ((x * (m_pre + 1 ) ) + (y - 1 ) ) (replace_Znth (((x * (m_pre + 1 ) ) + y )) ((((Znth (((x - 1 ) * (m_pre + 1 ) ) + y ) kl_2 0) + (Znth ((x * (m_pre + 1 ) ) + (y - 1 ) ) kl_2 0) ) % ( 998244853 ) )) (kl_2)) 0) ) % ( 998244853 ) ) + 998244853 ) % ( 998244853 ) )) (dl_2)))) = ((n_pre + 1 ) * (m_pre + 1 ) ))
.

Definition solver_entail_wit_11_1_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (y: Z) (x: Z) (dl_2: (@list Z)) (kl_2: (@list Z)) (il_2: (@list Z)) (fl_2: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl_2)) = (N + 1 ))) (PreH24 : ((Zlength (il_2)) = (N + 1 ))) (PreH25 : ((Zlength (kl_2)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl_2)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl_2 (N + 1 ) )) (PreH28 : (P080InverseFactorials il_2 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl_2) (0))) /\ ((Znth (j) (fl_2) (0)) < 998244853)) /\ (0 <= (Znth (j) (il_2) (0)))) /\ ((Znth (j) (il_2) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl_2) (0))) /\ ((Znth (j_2) (kl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl_2) (0)))) /\ ((Znth (j_2) (dl_2) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl_2 dl_2 )) ,
  ((Zlength ((replace_Znth (((x * (m_pre + 1 ) ) + y )) ((((Znth (((x - 1 ) * (m_pre + 1 ) ) + y ) kl_2 0) + (Znth ((x * (m_pre + 1 ) ) + (y - 1 ) ) kl_2 0) ) % ( 998244853 ) )) (kl_2)))) = ((n_pre + 1 ) * (m_pre + 1 ) ))
.

Definition solver_entail_wit_11_2 := 
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl_2: (@list Z)) (kl_2: (@list Z)) (il_2: (@list Z)) (fl_2: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl_2)) = (N + 1 ))) (PreH24 : ((Zlength (il_2)) = (N + 1 ))) (PreH25 : ((Zlength (kl_2)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl_2)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl_2 (N + 1 ) )) (PreH28 : (P080InverseFactorials il_2 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl_2) (0))) /\ ((Znth (j) (fl_2) (0)) < 998244853)) /\ (0 <= (Znth (j) (il_2) (0)))) /\ ((Znth (j) (il_2) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl_2) (0))) /\ ((Znth (j_2) (kl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl_2) (0)))) /\ ((Znth (j_2) (dl_2) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl_2 dl_2 )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) (((((((((((((Znth ((x + y ) - 1 ) fl_2 0) * (Znth y il_2 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il_2 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * W ) + y ) dl_2 0) ) + (Znth ((x * W ) + (y - 1 ) ) dl_2 0) ) - (((((Znth ((x + y ) - 1 ) fl_2 0) * (Znth x il_2 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il_2 0) ) % ( 998244853 ) ) ) + (Znth ((x * W ) + (y - 1 ) ) kl_2 0) ) % ( 998244853 ) ) + 998244853 ) % ( 998244853 ) )) (dl_2)) )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl_2 )
  **  (Int64Array.full ifac (N + 1 ) il_2 )
  **  (Int64Array.full fac (N + 1 ) fl_2 )
|--
  EX (dl: (@list Z))  (kl: (@list Z))  (il: (@list Z))  (fl: (@list Z)) ,
  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (1 <= (y + 1 )) ” 
  &&  “ ((y + 1 ) <= (m_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre x (y + 1 ) kl dl ) ”
  &&  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
) \/
(
forall (m_pre: Z) (n_pre: Z) (y: Z) (x: Z) (dl_2: (@list Z)) (kl_2: (@list Z)) (il_2: (@list Z)) (fl_2: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl_2)) = (N + 1 ))) (PreH24 : ((Zlength (il_2)) = (N + 1 ))) (PreH25 : ((Zlength (kl_2)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl_2)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl_2 (N + 1 ) )) (PreH28 : (P080InverseFactorials il_2 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl_2) (0))) /\ ((Znth (j) (fl_2) (0)) < 998244853)) /\ (0 <= (Znth (j) (il_2) (0)))) /\ ((Znth (j) (il_2) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl_2) (0))) /\ ((Znth (j_2) (kl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl_2) (0)))) /\ ((Znth (j_2) (dl_2) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl_2 dl_2 )) ,
  TT && emp 
|--
  “ (P080Tables n_pre m_pre x (y + 1 ) kl_2 (replace_Znth (((x * (m_pre + 1 ) ) + y )) (((((((((((((Znth ((x + y ) - 1 ) fl_2 0) * (Znth y il_2 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il_2 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * (m_pre + 1 ) ) + y ) dl_2 0) ) + (Znth ((x * (m_pre + 1 ) ) + (y - 1 ) ) dl_2 0) ) - (((((Znth ((x + y ) - 1 ) fl_2 0) * (Znth x il_2 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il_2 0) ) % ( 998244853 ) ) ) + (Znth ((x * (m_pre + 1 ) ) + (y - 1 ) ) kl_2 0) ) % ( 998244853 ) ) + 998244853 ) % ( 998244853 ) )) (dl_2)) ) ” 
  &&  “ ((Zlength ((replace_Znth (((x * (m_pre + 1 ) ) + y )) (((((((((((((Znth ((x + y ) - 1 ) fl_2 0) * (Znth y il_2 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il_2 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * (m_pre + 1 ) ) + y ) dl_2 0) ) + (Znth ((x * (m_pre + 1 ) ) + (y - 1 ) ) dl_2 0) ) - (((((Znth ((x + y ) - 1 ) fl_2 0) * (Znth x il_2 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il_2 0) ) % ( 998244853 ) ) ) + (Znth ((x * (m_pre + 1 ) ) + (y - 1 ) ) kl_2 0) ) % ( 998244853 ) ) + 998244853 ) % ( 998244853 ) )) (dl_2)))) = ((n_pre + 1 ) * (m_pre + 1 ) )) ”
  &&  emp
).

Definition solver_entail_wit_11_2_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (y: Z) (x: Z) (dl_2: (@list Z)) (kl_2: (@list Z)) (il_2: (@list Z)) (fl_2: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl_2)) = (N + 1 ))) (PreH24 : ((Zlength (il_2)) = (N + 1 ))) (PreH25 : ((Zlength (kl_2)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl_2)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl_2 (N + 1 ) )) (PreH28 : (P080InverseFactorials il_2 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl_2) (0))) /\ ((Znth (j) (fl_2) (0)) < 998244853)) /\ (0 <= (Znth (j) (il_2) (0)))) /\ ((Znth (j) (il_2) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl_2) (0))) /\ ((Znth (j_2) (kl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl_2) (0)))) /\ ((Znth (j_2) (dl_2) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl_2 dl_2 )) ,
  (P080Tables n_pre m_pre x (y + 1 ) kl_2 (replace_Znth (((x * (m_pre + 1 ) ) + y )) (((((((((((((Znth ((x + y ) - 1 ) fl_2 0) * (Znth y il_2 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il_2 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * (m_pre + 1 ) ) + y ) dl_2 0) ) + (Znth ((x * (m_pre + 1 ) ) + (y - 1 ) ) dl_2 0) ) - (((((Znth ((x + y ) - 1 ) fl_2 0) * (Znth x il_2 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il_2 0) ) % ( 998244853 ) ) ) + (Znth ((x * (m_pre + 1 ) ) + (y - 1 ) ) kl_2 0) ) % ( 998244853 ) ) + 998244853 ) % ( 998244853 ) )) (dl_2)) )
.

Definition solver_entail_wit_11_2_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (y: Z) (x: Z) (dl_2: (@list Z)) (kl_2: (@list Z)) (il_2: (@list Z)) (fl_2: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl_2)) = (N + 1 ))) (PreH24 : ((Zlength (il_2)) = (N + 1 ))) (PreH25 : ((Zlength (kl_2)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl_2)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl_2 (N + 1 ) )) (PreH28 : (P080InverseFactorials il_2 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl_2) (0))) /\ ((Znth (j) (fl_2) (0)) < 998244853)) /\ (0 <= (Znth (j) (il_2) (0)))) /\ ((Znth (j) (il_2) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl_2) (0))) /\ ((Znth (j_2) (kl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl_2) (0)))) /\ ((Znth (j_2) (dl_2) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl_2 dl_2 )) ,
  ((Zlength ((replace_Znth (((x * (m_pre + 1 ) ) + y )) (((((((((((((Znth ((x + y ) - 1 ) fl_2 0) * (Znth y il_2 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - y ) il_2 0) ) % ( 998244853 ) ) + (Znth (((x - 1 ) * (m_pre + 1 ) ) + y ) dl_2 0) ) + (Znth ((x * (m_pre + 1 ) ) + (y - 1 ) ) dl_2 0) ) - (((((Znth ((x + y ) - 1 ) fl_2 0) * (Znth x il_2 0) ) % ( 998244853 ) ) * (Znth (((x + y ) - 1 ) - x ) il_2 0) ) % ( 998244853 ) ) ) + (Znth ((x * (m_pre + 1 ) ) + (y - 1 ) ) kl_2 0) ) % ( 998244853 ) ) + 998244853 ) % ( 998244853 ) )) (dl_2)))) = ((n_pre + 1 ) * (m_pre + 1 ) ))
.

Definition solver_entail_wit_12 := 
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl_2: (@list Z)) (kl_2: (@list Z)) (il_2: (@list Z)) (fl_2: (@list Z)) (W: Z) (N: Z) (PreH1 : (y > m_pre)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (W = (m_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 2000)) (PreH8 : ((Zlength (fl_2)) = (N + 1 ))) (PreH9 : ((Zlength (il_2)) = (N + 1 ))) (PreH10 : ((Zlength (kl_2)) = ((n_pre + 1 ) * W ))) (PreH11 : ((Zlength (dl_2)) = ((n_pre + 1 ) * W ))) (PreH12 : (P080Factorials fl_2 (N + 1 ) )) (PreH13 : (P080InverseFactorials il_2 0 (N + 1 ) )) (PreH14 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (N + 1 ))) -> ((((0 <= (Znth (j_3) (fl_2) (0))) /\ ((Znth (j_3) (fl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_3) (il_2) (0)))) /\ ((Znth (j_3) (il_2) (0)) < 998244853)))) (PreH15 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_4) (kl_2) (0))) /\ ((Znth (j_4) (kl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_4) (dl_2) (0)))) /\ ((Znth (j_4) (dl_2) (0)) < 998244853)))) (PreH16 : (1 <= x)) (PreH17 : (x <= n_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= (m_pre + 1 ))) (PreH20 : (P080Tables n_pre m_pre x y kl_2 dl_2 )) ,
  (Int64Array.full fac (N + 1 ) fl_2 )
  **  (Int64Array.full ifac (N + 1 ) il_2 )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl_2 )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl_2 )
|--
  EX (dl: (@list Z))  (kl: (@list Z))  (il: (@list Z))  (fl: (@list Z)) ,
  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= (x + 1 )) ” 
  &&  “ ((x + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre (x + 1 ) 0 kl dl ) ”
  &&  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
) \/
(
forall (m_pre: Z) (n_pre: Z) (y: Z) (x: Z) (dl_2: (@list Z)) (kl_2: (@list Z)) (il_2: (@list Z)) (fl_2: (@list Z)) (W: Z) (N: Z) (PreH1 : (y > m_pre)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (W = (m_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 2000)) (PreH8 : ((Zlength (fl_2)) = (N + 1 ))) (PreH9 : ((Zlength (il_2)) = (N + 1 ))) (PreH10 : ((Zlength (kl_2)) = ((n_pre + 1 ) * W ))) (PreH11 : ((Zlength (dl_2)) = ((n_pre + 1 ) * W ))) (PreH12 : (P080Factorials fl_2 (N + 1 ) )) (PreH13 : (P080InverseFactorials il_2 0 (N + 1 ) )) (PreH14 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (N + 1 ))) -> ((((0 <= (Znth (j_3) (fl_2) (0))) /\ ((Znth (j_3) (fl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_3) (il_2) (0)))) /\ ((Znth (j_3) (il_2) (0)) < 998244853)))) (PreH15 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_4) (kl_2) (0))) /\ ((Znth (j_4) (kl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_4) (dl_2) (0)))) /\ ((Znth (j_4) (dl_2) (0)) < 998244853)))) (PreH16 : (1 <= x)) (PreH17 : (x <= n_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= (m_pre + 1 ))) (PreH20 : (P080Tables n_pre m_pre x y kl_2 dl_2 )) ,
  TT && emp 
|--
  “ (P080Tables n_pre m_pre (x + 1 ) 0 kl_2 dl_2 ) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl_2) (0))) /\ ((Znth (j_2) (kl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl_2) (0)))) /\ ((Znth (j_2) (dl_2) (0)) < 998244853))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl_2) (0))) /\ ((Znth (j) (fl_2) (0)) < 998244853)) /\ (0 <= (Znth (j) (il_2) (0)))) /\ ((Znth (j) (il_2) (0)) < 998244853))) ”
  &&  emp
).

Definition solver_entail_wit_12_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (y: Z) (x: Z) (dl_2: (@list Z)) (kl_2: (@list Z)) (il_2: (@list Z)) (fl_2: (@list Z)) (W: Z) (N: Z) (PreH1 : (y > m_pre)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (W = (m_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 2000)) (PreH8 : ((Zlength (fl_2)) = (N + 1 ))) (PreH9 : ((Zlength (il_2)) = (N + 1 ))) (PreH10 : ((Zlength (kl_2)) = ((n_pre + 1 ) * W ))) (PreH11 : ((Zlength (dl_2)) = ((n_pre + 1 ) * W ))) (PreH12 : (P080Factorials fl_2 (N + 1 ) )) (PreH13 : (P080InverseFactorials il_2 0 (N + 1 ) )) (PreH14 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (N + 1 ))) -> ((((0 <= (Znth (j_3) (fl_2) (0))) /\ ((Znth (j_3) (fl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_3) (il_2) (0)))) /\ ((Znth (j_3) (il_2) (0)) < 998244853)))) (PreH15 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_4) (kl_2) (0))) /\ ((Znth (j_4) (kl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_4) (dl_2) (0)))) /\ ((Znth (j_4) (dl_2) (0)) < 998244853)))) (PreH16 : (1 <= x)) (PreH17 : (x <= n_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= (m_pre + 1 ))) (PreH20 : (P080Tables n_pre m_pre x y kl_2 dl_2 )) ,
  (P080Tables n_pre m_pre (x + 1 ) 0 kl_2 dl_2 )
.

Definition solver_entail_wit_12_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (y: Z) (x: Z) (dl_2: (@list Z)) (kl_2: (@list Z)) (il_2: (@list Z)) (fl_2: (@list Z)) (W: Z) (N: Z) (PreH1 : (y > m_pre)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (W = (m_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 2000)) (PreH8 : ((Zlength (fl_2)) = (N + 1 ))) (PreH9 : ((Zlength (il_2)) = (N + 1 ))) (PreH10 : ((Zlength (kl_2)) = ((n_pre + 1 ) * W ))) (PreH11 : ((Zlength (dl_2)) = ((n_pre + 1 ) * W ))) (PreH12 : (P080Factorials fl_2 (N + 1 ) )) (PreH13 : (P080InverseFactorials il_2 0 (N + 1 ) )) (PreH14 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (N + 1 ))) -> ((((0 <= (Znth (j_3) (fl_2) (0))) /\ ((Znth (j_3) (fl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_3) (il_2) (0)))) /\ ((Znth (j_3) (il_2) (0)) < 998244853)))) (PreH15 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_4) (kl_2) (0))) /\ ((Znth (j_4) (kl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_4) (dl_2) (0)))) /\ ((Znth (j_4) (dl_2) (0)) < 998244853)))) (PreH16 : (1 <= x)) (PreH17 : (x <= n_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= (m_pre + 1 ))) (PreH20 : (P080Tables n_pre m_pre x y kl_2 dl_2 )) ,
  forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl_2) (0))) /\ ((Znth (j_2) (kl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl_2) (0)))) /\ ((Znth (j_2) (dl_2) (0)) < 998244853)))
.

Definition solver_entail_wit_12_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (y: Z) (x: Z) (dl_2: (@list Z)) (kl_2: (@list Z)) (il_2: (@list Z)) (fl_2: (@list Z)) (W: Z) (N: Z) (PreH1 : (y > m_pre)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (W = (m_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 2000)) (PreH8 : ((Zlength (fl_2)) = (N + 1 ))) (PreH9 : ((Zlength (il_2)) = (N + 1 ))) (PreH10 : ((Zlength (kl_2)) = ((n_pre + 1 ) * W ))) (PreH11 : ((Zlength (dl_2)) = ((n_pre + 1 ) * W ))) (PreH12 : (P080Factorials fl_2 (N + 1 ) )) (PreH13 : (P080InverseFactorials il_2 0 (N + 1 ) )) (PreH14 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (N + 1 ))) -> ((((0 <= (Znth (j_3) (fl_2) (0))) /\ ((Znth (j_3) (fl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_3) (il_2) (0)))) /\ ((Znth (j_3) (il_2) (0)) < 998244853)))) (PreH15 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_4) (kl_2) (0))) /\ ((Znth (j_4) (kl_2) (0)) < 998244853)) /\ (0 <= (Znth (j_4) (dl_2) (0)))) /\ ((Znth (j_4) (dl_2) (0)) < 998244853)))) (PreH16 : (1 <= x)) (PreH17 : (x <= n_pre)) (PreH18 : (1 <= y)) (PreH19 : (y <= (m_pre + 1 ))) (PreH20 : (P080Tables n_pre m_pre x y kl_2 dl_2 )) ,
  forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl_2) (0))) /\ ((Znth (j) (fl_2) (0)) < 998244853)) /\ (0 <= (Znth (j) (il_2) (0)))) /\ ((Znth (j) (il_2) (0)) < 998244853)))
.

Definition solver_entail_wit_13 := 
(
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x > n_pre)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (W = (m_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 2000)) (PreH8 : ((Zlength (fl)) = (N + 1 ))) (PreH9 : ((Zlength (il)) = (N + 1 ))) (PreH10 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH11 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH12 : (P080Factorials fl (N + 1 ) )) (PreH13 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH16 : (1 <= x)) (PreH17 : (x <= (n_pre + 1 ))) (PreH18 : (P080Tables n_pre m_pre x 0 kl dl )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (0 <= ((n_pre * W ) + m_pre )) ” 
  &&  “ (((n_pre * W ) + m_pre ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (N >= INT_MIN) ” 
  &&  “ (x > n_pre) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= (n_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre x 0 kl dl ) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "W" ) )) # Int  |-> W)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.full ifac (N + 1 ) il )
  **  ((( &( "K" ) )) # Ptr  |-> K)
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  ((( &( "D" ) )) # Ptr  |-> D)
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
) \/
(
forall (m_pre: Z) (n_pre: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (W <= INT_MAX)) (PreH2 : (N <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (W >= INT_MIN)) (PreH6 : (N >= INT_MIN)) (PreH7 : (m_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (x > n_pre)) (PreH10 : (N = (n_pre + m_pre ))) (PreH11 : (W = (m_pre + 1 ))) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (0 <= m_pre)) (PreH15 : (m_pre <= 2000)) (PreH16 : ((Zlength (fl)) = (N + 1 ))) (PreH17 : ((Zlength (il)) = (N + 1 ))) (PreH18 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH19 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH20 : (P080Factorials fl (N + 1 ) )) (PreH21 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH22 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH23 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH24 : (1 <= x)) (PreH25 : (x <= (n_pre + 1 ))) (PreH26 : (P080Tables n_pre m_pre x 0 kl dl )) ,
  TT && emp 
|--
  “ (((n_pre * (m_pre + 1 ) ) + m_pre ) < ((n_pre + 1 ) * (m_pre + 1 ) )) ”
  &&  emp
).

Definition solver_entail_wit_13_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (W <= INT_MAX)) (PreH2 : (N <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (W >= INT_MIN)) (PreH6 : (N >= INT_MIN)) (PreH7 : (m_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (x > n_pre)) (PreH10 : (N = (n_pre + m_pre ))) (PreH11 : (W = (m_pre + 1 ))) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (0 <= m_pre)) (PreH15 : (m_pre <= 2000)) (PreH16 : ((Zlength (fl)) = (N + 1 ))) (PreH17 : ((Zlength (il)) = (N + 1 ))) (PreH18 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH19 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH20 : (P080Factorials fl (N + 1 ) )) (PreH21 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH22 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH23 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH24 : (1 <= x)) (PreH25 : (x <= (n_pre + 1 ))) (PreH26 : (P080Tables n_pre m_pre x 0 kl dl )) ,
  (((n_pre * (m_pre + 1 ) ) + m_pre ) < ((n_pre + 1 ) * (m_pre + 1 ) ))
.

Definition solver_return_wit_1 := 
(
forall (m_pre: Z) (n_pre: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (0 <= ((n_pre * W ) + m_pre ))) (PreH2 : (((n_pre * W ) + m_pre ) < ((n_pre + 1 ) * W ))) (PreH3 : (N <= INT_MAX)) (PreH4 : (N >= INT_MIN)) (PreH5 : (x > n_pre)) (PreH6 : (N = (n_pre + m_pre ))) (PreH7 : (W = (m_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : (0 <= m_pre)) (PreH11 : (m_pre <= 2000)) (PreH12 : ((Zlength (fl)) = (N + 1 ))) (PreH13 : ((Zlength (il)) = (N + 1 ))) (PreH14 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH15 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH16 : (P080Factorials fl (N + 1 ) )) (PreH17 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH18 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH19 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH20 : (1 <= x)) (PreH21 : (x <= (n_pre + 1 ))) (PreH22 : (P080Tables n_pre m_pre x 0 kl dl )) ,
  TT && emp 
|--
  “ (Spec n_pre m_pre (Znth ((n_pre * W ) + m_pre ) dl 0) ) ”
  &&  emp
) \/
(
forall (m_pre: Z) (n_pre: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (0 <= ((n_pre * W ) + m_pre ))) (PreH2 : (((n_pre * W ) + m_pre ) < ((n_pre + 1 ) * W ))) (PreH3 : (N <= INT_MAX)) (PreH4 : (N >= INT_MIN)) (PreH5 : (x > n_pre)) (PreH6 : (N = (n_pre + m_pre ))) (PreH7 : (W = (m_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : (0 <= m_pre)) (PreH11 : (m_pre <= 2000)) (PreH12 : ((Zlength (fl)) = (N + 1 ))) (PreH13 : ((Zlength (il)) = (N + 1 ))) (PreH14 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH15 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH16 : (P080Factorials fl (N + 1 ) )) (PreH17 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH18 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH19 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH20 : (1 <= x)) (PreH21 : (x <= (n_pre + 1 ))) (PreH22 : (P080Tables n_pre m_pre x 0 kl dl )) ,
  TT && emp 
|--
  “ (Spec n_pre m_pre (Znth ((n_pre * (m_pre + 1 ) ) + m_pre ) dl 0) ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (0 <= ((n_pre * W ) + m_pre ))) (PreH2 : (((n_pre * W ) + m_pre ) < ((n_pre + 1 ) * W ))) (PreH3 : (N <= INT_MAX)) (PreH4 : (N >= INT_MIN)) (PreH5 : (x > n_pre)) (PreH6 : (N = (n_pre + m_pre ))) (PreH7 : (W = (m_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : (0 <= m_pre)) (PreH11 : (m_pre <= 2000)) (PreH12 : ((Zlength (fl)) = (N + 1 ))) (PreH13 : ((Zlength (il)) = (N + 1 ))) (PreH14 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH15 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH16 : (P080Factorials fl (N + 1 ) )) (PreH17 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH18 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH19 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH20 : (1 <= x)) (PreH21 : (x <= (n_pre + 1 ))) (PreH22 : (P080Tables n_pre m_pre x 0 kl dl )) ,
  (Spec n_pre m_pre (Znth ((n_pre * (m_pre + 1 ) ) + m_pre ) dl 0) )
.

Definition solver_partial_solve_wit_1_pure := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 2000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 2000)) ,
  ((( &( "ifac" ) )) # Ptr  |->_)
  **  (Int64Array.undef_full retval ((n_pre + m_pre ) + 1 ) )
  **  ((( &( "fac" ) )) # Ptr  |-> retval)
  **  ((( &( "N" ) )) # Int  |-> (n_pre + m_pre ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
|--
  “ (0 <= ((n_pre + m_pre ) + 1 )) ” 
  &&  “ ((((n_pre + m_pre ) + 1 ) * sizeof(INT64) ) = (((n_pre + m_pre ) + 1 ) * sizeof(INT64) )) ”
.

Definition solver_partial_solve_wit_1_aux := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 2000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 2000)) ,
  (Int64Array.undef_full retval ((n_pre + m_pre ) + 1 ) )
|--
  “ (0 <= ((n_pre + m_pre ) + 1 )) ” 
  &&  “ ((((n_pre + m_pre ) + 1 ) * sizeof(INT64) ) = (((n_pre + m_pre ) + 1 ) * sizeof(INT64) )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ”
  &&  (Int64Array.undef_full retval ((n_pre + m_pre ) + 1 ) )
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2_pure := 
forall (m_pre: Z) (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 2000)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= 2000)) ,
  ((( &( "fac" ) )) # Ptr  |->_)
  **  ((( &( "N" ) )) # Int  |-> (n_pre + m_pre ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
|--
  “ (0 <= ((n_pre + m_pre ) + 1 )) ” 
  &&  “ ((((n_pre + m_pre ) + 1 ) * sizeof(INT64) ) = (((n_pre + m_pre ) + 1 ) * sizeof(INT64) )) ”
.

Definition solver_partial_solve_wit_2_aux := 
forall (m_pre: Z) (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 2000)) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= 2000)) ,
  TT && emp 
|--
  “ (0 <= ((n_pre + m_pre ) + 1 )) ” 
  &&  “ ((((n_pre + m_pre ) + 1 ) * sizeof(INT64) ) = (((n_pre + m_pre ) + 1 ) * sizeof(INT64) )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ”
  &&  emp
.

Definition solver_partial_solve_wit_2 := solver_partial_solve_wit_2_pure -> solver_partial_solve_wit_2_aux.

Definition solver_partial_solve_wit_3 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000)) ,
  (Int64Array.undef_full retval_2 ((n_pre + m_pre ) + 1 ) )
  **  (Int64Array.undef_full retval ((n_pre + m_pre ) + 1 ) )
|--
  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ”
  &&  (((retval + (0 * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg retval 1 ((n_pre + m_pre ) + 1 ) )
  **  (Int64Array.undef_full retval_2 ((n_pre + m_pre ) + 1 ) )
.

Definition solver_partial_solve_wit_4 := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (i <= N)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000)) (PreH7 : (1 <= i)) (PreH8 : (i <= (N + 1 ))) (PreH9 : ((Zlength (fl)) = i)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((((Znth (j) (fl) (0)) = ((P080Factorial (j)) % ( 998244853 ) )) /\ (0 <= (Znth (j) (fl) (0)))) /\ ((Znth (j) (fl) (0)) < 998244853)))) ,
  (Int64Array.seg fac 0 i fl )
  **  (Int64Array.undef_seg fac i (N + 1 ) )
  **  (Int64Array.undef_full ifac (N + 1 ) )
|--
  “ (i <= N) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (N + 1 )) ” 
  &&  “ ((Zlength (fl)) = i) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((((Znth (j) (fl) (0)) = ((P080Factorial (j)) % ( 998244853 ) )) /\ (0 <= (Znth (j) (fl) (0)))) /\ ((Znth (j) (fl) (0)) < 998244853))) ”
  &&  (((fac + ((i - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth ((i - 1 ) - 0 ) fl 0))
  **  (Int64Array.missing_i fac (i - 1 ) 0 i fl )
  **  (Int64Array.undef_seg fac i (N + 1 ) )
  **  (Int64Array.undef_full ifac (N + 1 ) )
.

Definition solver_partial_solve_wit_5 := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (i <= N)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000)) (PreH7 : (1 <= i)) (PreH8 : (i <= (N + 1 ))) (PreH9 : ((Zlength (fl)) = i)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((((Znth (j) (fl) (0)) = ((P080Factorial (j)) % ( 998244853 ) )) /\ (0 <= (Znth (j) (fl) (0)))) /\ ((Znth (j) (fl) (0)) < 998244853)))) ,
  (Int64Array.seg fac 0 i fl )
  **  (Int64Array.undef_seg fac i (N + 1 ) )
  **  (Int64Array.undef_full ifac (N + 1 ) )
|--
  “ (i <= N) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (N + 1 )) ” 
  &&  “ ((Zlength (fl)) = i) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((((Znth (j) (fl) (0)) = ((P080Factorial (j)) % ( 998244853 ) )) /\ (0 <= (Znth (j) (fl) (0)))) /\ ((Znth (j) (fl) (0)) < 998244853))) ”
  &&  (((fac + (i * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg fac (i + 1 ) (N + 1 ) )
  **  (Int64Array.seg fac 0 i fl )
  **  (Int64Array.undef_full ifac (N + 1 ) )
.

Definition solver_partial_solve_wit_6 := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (i > N)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000)) (PreH7 : (1 <= i)) (PreH8 : (i <= (N + 1 ))) (PreH9 : ((Zlength (fl)) = i)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((((Znth (j) (fl) (0)) = ((P080Factorial (j)) % ( 998244853 ) )) /\ (0 <= (Znth (j) (fl) (0)))) /\ ((Znth (j) (fl) (0)) < 998244853)))) ,
  (Int64Array.seg fac 0 i fl )
  **  (Int64Array.undef_seg fac i (N + 1 ) )
  **  (Int64Array.undef_full ifac (N + 1 ) )
|--
  “ (i > N) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (N + 1 )) ” 
  &&  “ ((Zlength (fl)) = i) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((((Znth (j) (fl) (0)) = ((P080Factorial (j)) % ( 998244853 ) )) /\ (0 <= (Znth (j) (fl) (0)))) /\ ((Znth (j) (fl) (0)) < 998244853))) ”
  &&  (((fac + (N * sizeof(INT64)))) # Int64  |-> (Znth (N - 0 ) fl 0))
  **  (Int64Array.missing_i fac N 0 i fl )
  **  (Int64Array.undef_full ifac (N + 1 ) )
.

Definition solver_partial_solve_wit_7_pure := 
(
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (i > N)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000)) (PreH7 : (1 <= i)) (PreH8 : (i <= (N + 1 ))) (PreH9 : ((Zlength (fl)) = i)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((((Znth (j) (fl) (0)) = ((P080Factorial (j)) % ( 998244853 ) )) /\ (0 <= (Znth (j) (fl) (0)))) /\ ((Znth (j) (fl) (0)) < 998244853)))) ,
  (Int64Array.seg fac 0 i fl )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.undef_full ifac (N + 1 ) )
|--
  “ (0 <= (Znth (N - 0 ) fl 0)) ” 
  &&  “ ((Znth (N - 0 ) fl 0) < 998244853) ” 
  &&  “ (0 <= (998244853 - 2 )) ” 
  &&  “ ((998244853 - 2 ) <= 998244853) ” 
  &&  “ ((Znth ((n_pre + m_pre ) - 0 ) fl 0) < 998244853) ” 
  &&  “ (0 <= (Znth ((n_pre + m_pre ) - 0 ) fl 0)) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (N <= INT_MAX)) (PreH2 : (m_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (N >= INT_MIN)) (PreH5 : (m_pre >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i > N)) (PreH8 : (N = (n_pre + m_pre ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 2000)) (PreH11 : (0 <= m_pre)) (PreH12 : (m_pre <= 2000)) (PreH13 : (1 <= i)) (PreH14 : (i <= (N + 1 ))) (PreH15 : ((Zlength (fl)) = i)) (PreH16 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((((Znth (j) (fl) (0)) = ((P080Factorial (j)) % ( 998244853 ) )) /\ (0 <= (Znth (j) (fl) (0)))) /\ ((Znth (j) (fl) (0)) < 998244853)))) ,
  (Int64Array.seg fac 0 i fl )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.undef_full ifac (N + 1 ) )
|--
  “ (0 <= (Znth ((n_pre + m_pre ) - 0 ) fl 0)) ” 
  &&  “ ((Znth ((n_pre + m_pre ) - 0 ) fl 0) < 998244853) ” 
  &&  “ ((Znth ((n_pre + m_pre ) - 0 ) fl 0) < 998244853) ” 
  &&  “ (0 <= (Znth ((n_pre + m_pre ) - 0 ) fl 0)) ”
).

Definition solver_partial_solve_wit_7_pure_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (N <= INT_MAX)) (PreH2 : (m_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (N >= INT_MIN)) (PreH5 : (m_pre >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i > N)) (PreH8 : (N = (n_pre + m_pre ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 2000)) (PreH11 : (0 <= m_pre)) (PreH12 : (m_pre <= 2000)) (PreH13 : (1 <= i)) (PreH14 : (i <= (N + 1 ))) (PreH15 : ((Zlength (fl)) = i)) (PreH16 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((((Znth (j) (fl) (0)) = ((P080Factorial (j)) % ( 998244853 ) )) /\ (0 <= (Znth (j) (fl) (0)))) /\ ((Znth (j) (fl) (0)) < 998244853)))) ,
  (Int64Array.seg fac 0 i fl )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.undef_full ifac (N + 1 ) )
|--
  “ (0 <= (Znth ((n_pre + m_pre ) - 0 ) fl 0)) ”
.

Definition solver_partial_solve_wit_7_pure_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (N <= INT_MAX)) (PreH2 : (m_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (N >= INT_MIN)) (PreH5 : (m_pre >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i > N)) (PreH8 : (N = (n_pre + m_pre ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 2000)) (PreH11 : (0 <= m_pre)) (PreH12 : (m_pre <= 2000)) (PreH13 : (1 <= i)) (PreH14 : (i <= (N + 1 ))) (PreH15 : ((Zlength (fl)) = i)) (PreH16 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((((Znth (j) (fl) (0)) = ((P080Factorial (j)) % ( 998244853 ) )) /\ (0 <= (Znth (j) (fl) (0)))) /\ ((Znth (j) (fl) (0)) < 998244853)))) ,
  (Int64Array.seg fac 0 i fl )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.undef_full ifac (N + 1 ) )
|--
  “ ((Znth ((n_pre + m_pre ) - 0 ) fl 0) < 998244853) ”
.

Definition solver_partial_solve_wit_7_pure_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (N <= INT_MAX)) (PreH2 : (m_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (N >= INT_MIN)) (PreH5 : (m_pre >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i > N)) (PreH8 : (N = (n_pre + m_pre ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 2000)) (PreH11 : (0 <= m_pre)) (PreH12 : (m_pre <= 2000)) (PreH13 : (1 <= i)) (PreH14 : (i <= (N + 1 ))) (PreH15 : ((Zlength (fl)) = i)) (PreH16 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((((Znth (j) (fl) (0)) = ((P080Factorial (j)) % ( 998244853 ) )) /\ (0 <= (Znth (j) (fl) (0)))) /\ ((Znth (j) (fl) (0)) < 998244853)))) ,
  (Int64Array.seg fac 0 i fl )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.undef_full ifac (N + 1 ) )
|--
  “ ((Znth ((n_pre + m_pre ) - 0 ) fl 0) < 998244853) ”
.

Definition solver_partial_solve_wit_7_pure_split_goal_4 := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (N <= INT_MAX)) (PreH2 : (m_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (N >= INT_MIN)) (PreH5 : (m_pre >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i > N)) (PreH8 : (N = (n_pre + m_pre ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 2000)) (PreH11 : (0 <= m_pre)) (PreH12 : (m_pre <= 2000)) (PreH13 : (1 <= i)) (PreH14 : (i <= (N + 1 ))) (PreH15 : ((Zlength (fl)) = i)) (PreH16 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((((Znth (j) (fl) (0)) = ((P080Factorial (j)) % ( 998244853 ) )) /\ (0 <= (Znth (j) (fl) (0)))) /\ ((Znth (j) (fl) (0)) < 998244853)))) ,
  (Int64Array.seg fac 0 i fl )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.undef_full ifac (N + 1 ) )
|--
  “ (0 <= (Znth ((n_pre + m_pre ) - 0 ) fl 0)) ”
.

Definition solver_partial_solve_wit_7_aux := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (i > N)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000)) (PreH7 : (1 <= i)) (PreH8 : (i <= (N + 1 ))) (PreH9 : ((Zlength (fl)) = i)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((((Znth (j) (fl) (0)) = ((P080Factorial (j)) % ( 998244853 ) )) /\ (0 <= (Znth (j) (fl) (0)))) /\ ((Znth (j) (fl) (0)) < 998244853)))) ,
  (Int64Array.seg fac 0 i fl )
  **  (Int64Array.undef_full ifac (N + 1 ) )
|--
  “ (0 <= (Znth (N - 0 ) fl 0)) ” 
  &&  “ ((Znth (N - 0 ) fl 0) < 998244853) ” 
  &&  “ (0 <= (998244853 - 2 )) ” 
  &&  “ ((998244853 - 2 ) <= 998244853) ” 
  &&  “ ((Znth ((n_pre + m_pre ) - 0 ) fl 0) < 998244853) ” 
  &&  “ (0 <= (Znth ((n_pre + m_pre ) - 0 ) fl 0)) ” 
  &&  “ (i > N) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (N + 1 )) ” 
  &&  “ ((Zlength (fl)) = i) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((((Znth (j) (fl) (0)) = ((P080Factorial (j)) % ( 998244853 ) )) /\ (0 <= (Znth (j) (fl) (0)))) /\ ((Znth (j) (fl) (0)) < 998244853))) ”
  &&  (Int64Array.seg fac 0 i fl )
  **  (Int64Array.undef_full ifac (N + 1 ) )
.

Definition solver_partial_solve_wit_7 := solver_partial_solve_wit_7_pure -> solver_partial_solve_wit_7_aux.

Definition solver_partial_solve_wit_8 := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (fl: (@list Z)) (i: Z) (N: Z) (retval: Z) (PreH1 : (retval = ((Z.pow ((Znth (N - 0 ) fl 0)) ((998244853 - 2 ))) % ( 998244853 ) ))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 998244853)) (PreH4 : (i > N)) (PreH5 : (N = (n_pre + m_pre ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (0 <= m_pre)) (PreH9 : (m_pre <= 2000)) (PreH10 : (1 <= i)) (PreH11 : (i <= (N + 1 ))) (PreH12 : ((Zlength (fl)) = i)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((((Znth (j) (fl) (0)) = ((P080Factorial (j)) % ( 998244853 ) )) /\ (0 <= (Znth (j) (fl) (0)))) /\ ((Znth (j) (fl) (0)) < 998244853)))) ,
  (Int64Array.seg fac 0 i fl )
  **  (Int64Array.undef_full ifac (N + 1 ) )
|--
  “ (retval = ((Z.pow ((Znth (N - 0 ) fl 0)) ((998244853 - 2 ))) % ( 998244853 ) )) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < 998244853) ” 
  &&  “ (i > N) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (N + 1 )) ” 
  &&  “ ((Zlength (fl)) = i) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((((Znth (j) (fl) (0)) = ((P080Factorial (j)) % ( 998244853 ) )) /\ (0 <= (Znth (j) (fl) (0)))) /\ ((Znth (j) (fl) (0)) < 998244853))) ”
  &&  (((ifac + (N * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_missing_i ifac N 0 (N + 1 ) )
  **  (Int64Array.seg fac 0 i fl )
.

Definition solver_partial_solve_wit_9 := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (il: (@list Z)) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (N = (n_pre + m_pre ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 2000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 2000)) (PreH6 : (0 <= i)) (PreH7 : (i <= N)) (PreH8 : ((Zlength (fl)) = (N + 1 ))) (PreH9 : ((Zlength (il)) = ((N + 1 ) - i ))) (PreH10 : (P080Factorials fl (N + 1 ) )) (PreH11 : (P080InverseFactorials il i (N + 1 ) )) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)))) (PreH13 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((N + 1 ) - i ))) -> ((0 <= (Znth (j_2) (il) (0))) /\ ((Znth (j_2) (il) (0)) < 998244853)))) (PreH14 : (i <> 0)) ,
  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.undef_seg ifac 0 i )
  **  (Int64Array.seg ifac i (N + 1 ) il )
|--
  “ (N = (n_pre + m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= N) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = ((N + 1 ) - i )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il i (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((N + 1 ) - i ))) -> ((0 <= (Znth (j_2) (il) (0))) /\ ((Znth (j_2) (il) (0)) < 998244853))) ” 
  &&  “ (i <> 0) ”
  &&  (((ifac + (i * sizeof(INT64)))) # Int64  |-> (Znth (i - i ) il 0))
  **  (Int64Array.missing_i ifac i i (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.undef_seg ifac 0 i )
.

Definition solver_partial_solve_wit_10 := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (il: (@list Z)) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (N = (n_pre + m_pre ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 2000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 2000)) (PreH6 : (0 <= i)) (PreH7 : (i <= N)) (PreH8 : ((Zlength (fl)) = (N + 1 ))) (PreH9 : ((Zlength (il)) = ((N + 1 ) - i ))) (PreH10 : (P080Factorials fl (N + 1 ) )) (PreH11 : (P080InverseFactorials il i (N + 1 ) )) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)))) (PreH13 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((N + 1 ) - i ))) -> ((0 <= (Znth (j_2) (il) (0))) /\ ((Znth (j_2) (il) (0)) < 998244853)))) (PreH14 : (i <> 0)) ,
  (Int64Array.seg ifac i (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.undef_seg ifac 0 i )
|--
  “ (N = (n_pre + m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= N) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = ((N + 1 ) - i )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il i (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((N + 1 ) - i ))) -> ((0 <= (Znth (j_2) (il) (0))) /\ ((Znth (j_2) (il) (0)) < 998244853))) ” 
  &&  “ (i <> 0) ”
  &&  (((ifac + ((i - 1 ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_missing_i ifac (i - 1 ) 0 i )
  **  (Int64Array.seg ifac i (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
.

Definition solver_partial_solve_wit_11_pure := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (il: (@list Z)) (fl: (@list Z)) (i: Z) (N: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000)) (PreH7 : (0 <= i)) (PreH8 : (i <= N)) (PreH9 : ((Zlength (fl)) = (N + 1 ))) (PreH10 : ((Zlength (il)) = ((N + 1 ) - i ))) (PreH11 : (P080Factorials fl (N + 1 ) )) (PreH12 : (P080InverseFactorials il i (N + 1 ) )) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)))) (PreH14 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((N + 1 ) - i ))) -> ((0 <= (Znth (j_2) (il) (0))) /\ ((Znth (j_2) (il) (0)) < 998244853)))) (PreH15 : (i = 0)) ,
  ((( &( "D" ) )) # Ptr  |->_)
  **  (Int64Array.full retval ((n_pre + 1 ) * (m_pre + 1 ) ) (repeat_Z (0) (((n_pre + 1 ) * (m_pre + 1 ) ))) )
  **  ((( &( "K" ) )) # Ptr  |-> retval)
  **  ((( &( "W" ) )) # Int  |-> (m_pre + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.seg ifac i (N + 1 ) il )
|--
  “ (0 <= ((n_pre + 1 ) * (m_pre + 1 ) )) ” 
  &&  “ (sizeof(INT64) = sizeof(INT64)) ”
.

Definition solver_partial_solve_wit_11_aux := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (il: (@list Z)) (fl: (@list Z)) (i: Z) (N: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 2000)) (PreH7 : (0 <= i)) (PreH8 : (i <= N)) (PreH9 : ((Zlength (fl)) = (N + 1 ))) (PreH10 : ((Zlength (il)) = ((N + 1 ) - i ))) (PreH11 : (P080Factorials fl (N + 1 ) )) (PreH12 : (P080InverseFactorials il i (N + 1 ) )) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)))) (PreH14 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((N + 1 ) - i ))) -> ((0 <= (Znth (j_2) (il) (0))) /\ ((Znth (j_2) (il) (0)) < 998244853)))) (PreH15 : (i = 0)) ,
  (Int64Array.full retval ((n_pre + 1 ) * (m_pre + 1 ) ) (repeat_Z (0) (((n_pre + 1 ) * (m_pre + 1 ) ))) )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.seg ifac i (N + 1 ) il )
|--
  “ (0 <= ((n_pre + 1 ) * (m_pre + 1 ) )) ” 
  &&  “ (sizeof(INT64) = sizeof(INT64)) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= N) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = ((N + 1 ) - i )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il i (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((N + 1 ) - i ))) -> ((0 <= (Znth (j_2) (il) (0))) /\ ((Znth (j_2) (il) (0)) < 998244853))) ” 
  &&  “ (i = 0) ”
  &&  (Int64Array.full retval ((n_pre + 1 ) * (m_pre + 1 ) ) (repeat_Z (0) (((n_pre + 1 ) * (m_pre + 1 ) ))) )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.seg ifac i (N + 1 ) il )
.

Definition solver_partial_solve_wit_11 := solver_partial_solve_wit_11_pure -> solver_partial_solve_wit_11_aux.

Definition solver_partial_solve_wit_12_pure := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (il: (@list Z)) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (N = (n_pre + m_pre ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 2000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 2000)) (PreH6 : (0 <= i)) (PreH7 : (i <= N)) (PreH8 : ((Zlength (fl)) = (N + 1 ))) (PreH9 : ((Zlength (il)) = ((N + 1 ) - i ))) (PreH10 : (P080Factorials fl (N + 1 ) )) (PreH11 : (P080InverseFactorials il i (N + 1 ) )) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)))) (PreH13 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((N + 1 ) - i ))) -> ((0 <= (Znth (j_2) (il) (0))) /\ ((Znth (j_2) (il) (0)) < 998244853)))) (PreH14 : (i = 0)) ,
  ((( &( "K" ) )) # Ptr  |->_)
  **  ((( &( "W" ) )) # Int  |-> (m_pre + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "fac" ) )) # Ptr  |-> fac)
  **  (Int64Array.full fac (N + 1 ) fl )
  **  ((( &( "ifac" ) )) # Ptr  |-> ifac)
  **  (Int64Array.undef_seg ifac 0 i )
  **  (Int64Array.seg ifac i (N + 1 ) il )
|--
  “ (0 <= ((n_pre + 1 ) * (m_pre + 1 ) )) ” 
  &&  “ (sizeof(INT64) = sizeof(INT64)) ”
.

Definition solver_partial_solve_wit_12_aux := 
forall (m_pre: Z) (n_pre: Z) (ifac: Z) (fac: Z) (il: (@list Z)) (fl: (@list Z)) (i: Z) (N: Z) (PreH1 : (N = (n_pre + m_pre ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 2000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 2000)) (PreH6 : (0 <= i)) (PreH7 : (i <= N)) (PreH8 : ((Zlength (fl)) = (N + 1 ))) (PreH9 : ((Zlength (il)) = ((N + 1 ) - i ))) (PreH10 : (P080Factorials fl (N + 1 ) )) (PreH11 : (P080InverseFactorials il i (N + 1 ) )) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)))) (PreH13 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((N + 1 ) - i ))) -> ((0 <= (Znth (j_2) (il) (0))) /\ ((Znth (j_2) (il) (0)) < 998244853)))) (PreH14 : (i = 0)) ,
  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.undef_seg ifac 0 i )
  **  (Int64Array.seg ifac i (N + 1 ) il )
|--
  “ (0 <= ((n_pre + 1 ) * (m_pre + 1 ) )) ” 
  &&  “ (sizeof(INT64) = sizeof(INT64)) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= N) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = ((N + 1 ) - i )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il i (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((N + 1 ) - i ))) -> ((0 <= (Znth (j_2) (il) (0))) /\ ((Znth (j_2) (il) (0)) < 998244853))) ” 
  &&  “ (i = 0) ”
  &&  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.seg ifac i (N + 1 ) il )
.

Definition solver_partial_solve_wit_12 := solver_partial_solve_wit_12_pure -> solver_partial_solve_wit_12_aux.

Definition solver_partial_solve_wit_13 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= m_pre)) (PreH2 : (N = (n_pre + m_pre ))) (PreH3 : (W = (m_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 2000)) (PreH8 : ((Zlength (fl)) = (N + 1 ))) (PreH9 : ((Zlength (il)) = (N + 1 ))) (PreH10 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH11 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH12 : (P080Factorials fl (N + 1 ) )) (PreH13 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH16 : (0 <= y)) (PreH17 : (y <= (m_pre + 1 ))) (PreH18 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < y)) -> ((Znth (j_3) (kl) (0)) = 1))) (PreH19 : forall (j_4: Z) , (((y <= j_4) /\ (j_4 < ((n_pre + 1 ) * W ))) -> ((Znth (j_4) (kl) (0)) = 0))) (PreH20 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < ((n_pre + 1 ) * W ))) -> ((Znth (j_5) (dl) (0)) = 0))) ,
  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (y <= m_pre) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (0 <= y) ” 
  &&  “ (y <= (m_pre + 1 )) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < y)) -> ((Znth (j_3) (kl) (0)) = 1)) ” 
  &&  “ forall (j_4: Z) , (((y <= j_4) /\ (j_4 < ((n_pre + 1 ) * W ))) -> ((Znth (j_4) (kl) (0)) = 0)) ” 
  &&  “ forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < ((n_pre + 1 ) * W ))) -> ((Znth (j_5) (dl) (0)) = 0)) ”
  &&  (((K + (((0 * W ) + y ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i K ((0 * W ) + y ) 0 ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
.

Definition solver_partial_solve_wit_14 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (0 <= (x * W ))) (PreH2 : ((x * W ) < ((n_pre + 1 ) * W ))) (PreH3 : (N <= INT_MAX)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (N >= INT_MIN)) (PreH6 : (m_pre >= INT_MIN)) (PreH7 : (x <= n_pre)) (PreH8 : (N = (n_pre + m_pre ))) (PreH9 : (W = (m_pre + 1 ))) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 2000)) (PreH12 : (0 <= m_pre)) (PreH13 : (m_pre <= 2000)) (PreH14 : ((Zlength (fl)) = (N + 1 ))) (PreH15 : ((Zlength (il)) = (N + 1 ))) (PreH16 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH17 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH18 : (P080Factorials fl (N + 1 ) )) (PreH19 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH20 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH21 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH22 : (1 <= x)) (PreH23 : (x <= (n_pre + 1 ))) (PreH24 : (P080Tables n_pre m_pre x 0 kl dl )) ,
  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (0 <= (x * W )) ” 
  &&  “ ((x * W ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (N >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= (n_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre x 0 kl dl ) ”
  &&  (((D + (((x * W ) + 0 ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i D ((x * W ) + 0 ) 0 ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
.

Definition solver_partial_solve_wit_15 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= y)) (PreH2 : (0 <= ((x * W ) + y ))) (PreH3 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH4 : (0 <= (((x - 1 ) * W ) + y ))) (PreH5 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH7 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH8 : (N <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (N >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (y <= m_pre)) (PreH13 : (N = (n_pre + m_pre ))) (PreH14 : (W = (m_pre + 1 ))) (PreH15 : (0 <= n_pre)) (PreH16 : (n_pre <= 2000)) (PreH17 : (0 <= m_pre)) (PreH18 : (m_pre <= 2000)) (PreH19 : ((Zlength (fl)) = (N + 1 ))) (PreH20 : ((Zlength (il)) = (N + 1 ))) (PreH21 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH22 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH23 : (P080Factorials fl (N + 1 ) )) (PreH24 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH25 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH26 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH27 : (1 <= x)) (PreH28 : (x <= n_pre)) (PreH29 : (1 <= y)) (PreH30 : (y <= (m_pre + 1 ))) (PreH31 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (x <= y) ” 
  &&  “ (0 <= ((x * W ) + y )) ” 
  &&  “ (((x * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= (((x - 1 ) * W ) + y )) ” 
  &&  “ ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= ((x * W ) + (y - 1 ) )) ” 
  &&  “ (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (N >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (y <= m_pre) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (1 <= y) ” 
  &&  “ (y <= (m_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre x y kl dl ) ”
  &&  (((K + ((((x - 1 ) * W ) + y ) * sizeof(INT64)))) # Int64  |-> (Znth (((x - 1 ) * W ) + y ) kl 0))
  **  (Int64Array.missing_i K (((x - 1 ) * W ) + y ) 0 ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
.

Definition solver_partial_solve_wit_16 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= y)) (PreH2 : (0 <= ((x * W ) + y ))) (PreH3 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH4 : (0 <= (((x - 1 ) * W ) + y ))) (PreH5 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH7 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH8 : (N <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (N >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (y <= m_pre)) (PreH13 : (N = (n_pre + m_pre ))) (PreH14 : (W = (m_pre + 1 ))) (PreH15 : (0 <= n_pre)) (PreH16 : (n_pre <= 2000)) (PreH17 : (0 <= m_pre)) (PreH18 : (m_pre <= 2000)) (PreH19 : ((Zlength (fl)) = (N + 1 ))) (PreH20 : ((Zlength (il)) = (N + 1 ))) (PreH21 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH22 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH23 : (P080Factorials fl (N + 1 ) )) (PreH24 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH25 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH26 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH27 : (1 <= x)) (PreH28 : (x <= n_pre)) (PreH29 : (1 <= y)) (PreH30 : (y <= (m_pre + 1 ))) (PreH31 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (x <= y) ” 
  &&  “ (0 <= ((x * W ) + y )) ” 
  &&  “ (((x * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= (((x - 1 ) * W ) + y )) ” 
  &&  “ ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= ((x * W ) + (y - 1 ) )) ” 
  &&  “ (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (N >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (y <= m_pre) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (1 <= y) ” 
  &&  “ (y <= (m_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre x y kl dl ) ”
  &&  (((K + (((x * W ) + (y - 1 ) ) * sizeof(INT64)))) # Int64  |-> (Znth ((x * W ) + (y - 1 ) ) kl 0))
  **  (Int64Array.missing_i K ((x * W ) + (y - 1 ) ) 0 ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
.

Definition solver_partial_solve_wit_17 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= y)) (PreH2 : (0 <= ((x * W ) + y ))) (PreH3 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH4 : (0 <= (((x - 1 ) * W ) + y ))) (PreH5 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH7 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH8 : (N <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (N >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (y <= m_pre)) (PreH13 : (N = (n_pre + m_pre ))) (PreH14 : (W = (m_pre + 1 ))) (PreH15 : (0 <= n_pre)) (PreH16 : (n_pre <= 2000)) (PreH17 : (0 <= m_pre)) (PreH18 : (m_pre <= 2000)) (PreH19 : ((Zlength (fl)) = (N + 1 ))) (PreH20 : ((Zlength (il)) = (N + 1 ))) (PreH21 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH22 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH23 : (P080Factorials fl (N + 1 ) )) (PreH24 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH25 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH26 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH27 : (1 <= x)) (PreH28 : (x <= n_pre)) (PreH29 : (1 <= y)) (PreH30 : (y <= (m_pre + 1 ))) (PreH31 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (x <= y) ” 
  &&  “ (0 <= ((x * W ) + y )) ” 
  &&  “ (((x * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= (((x - 1 ) * W ) + y )) ” 
  &&  “ ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= ((x * W ) + (y - 1 ) )) ” 
  &&  “ (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (N >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (y <= m_pre) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (1 <= y) ” 
  &&  “ (y <= (m_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre x y kl dl ) ”
  &&  (((K + (((x * W ) + y ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i K ((x * W ) + y ) 0 ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
.

Definition solver_partial_solve_wit_18 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (y <= ((x + y ) - 1 )) ” 
  &&  “ (y >= 0) ” 
  &&  “ (x <= y) ” 
  &&  “ (0 <= ((x * W ) + y )) ” 
  &&  “ (((x * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= (((x - 1 ) * W ) + y )) ” 
  &&  “ ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= ((x * W ) + (y - 1 ) )) ” 
  &&  “ (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (N >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (y <= m_pre) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (1 <= y) ” 
  &&  “ (y <= (m_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre x y kl dl ) ”
  &&  (((fac + (((x + y ) - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth ((x + y ) - 1 ) fl 0))
  **  (Int64Array.missing_i fac ((x + y ) - 1 ) 0 (N + 1 ) fl )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
.

Definition solver_partial_solve_wit_19 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (y <= ((x + y ) - 1 )) ” 
  &&  “ (y >= 0) ” 
  &&  “ (x <= y) ” 
  &&  “ (0 <= ((x * W ) + y )) ” 
  &&  “ (((x * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= (((x - 1 ) * W ) + y )) ” 
  &&  “ ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= ((x * W ) + (y - 1 ) )) ” 
  &&  “ (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (N >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (y <= m_pre) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (1 <= y) ” 
  &&  “ (y <= (m_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre x y kl dl ) ”
  &&  (((ifac + (y * sizeof(INT64)))) # Int64  |-> (Znth y il 0))
  **  (Int64Array.missing_i ifac y 0 (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
.

Definition solver_partial_solve_wit_20 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (y <= ((x + y ) - 1 )) ” 
  &&  “ (y >= 0) ” 
  &&  “ (x <= y) ” 
  &&  “ (0 <= ((x * W ) + y )) ” 
  &&  “ (((x * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= (((x - 1 ) * W ) + y )) ” 
  &&  “ ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= ((x * W ) + (y - 1 ) )) ” 
  &&  “ (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (N >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (y <= m_pre) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (1 <= y) ” 
  &&  “ (y <= (m_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre x y kl dl ) ”
  &&  (((ifac + ((((x + y ) - 1 ) - y ) * sizeof(INT64)))) # Int64  |-> (Znth (((x + y ) - 1 ) - y ) il 0))
  **  (Int64Array.missing_i ifac (((x + y ) - 1 ) - y ) 0 (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
.

Definition solver_partial_solve_wit_21 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (y <= ((x + y ) - 1 )) ” 
  &&  “ (y >= 0) ” 
  &&  “ (x <= y) ” 
  &&  “ (0 <= ((x * W ) + y )) ” 
  &&  “ (((x * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= (((x - 1 ) * W ) + y )) ” 
  &&  “ ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= ((x * W ) + (y - 1 ) )) ” 
  &&  “ (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (N >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (y <= m_pre) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (1 <= y) ” 
  &&  “ (y <= (m_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre x y kl dl ) ”
  &&  (((D + ((((x - 1 ) * W ) + y ) * sizeof(INT64)))) # Int64  |-> (Znth (((x - 1 ) * W ) + y ) dl 0))
  **  (Int64Array.missing_i D (((x - 1 ) * W ) + y ) 0 ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
.

Definition solver_partial_solve_wit_22 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x <= y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
|--
  “ (y <= ((x + y ) - 1 )) ” 
  &&  “ (y >= 0) ” 
  &&  “ (x <= y) ” 
  &&  “ (0 <= ((x * W ) + y )) ” 
  &&  “ (((x * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= (((x - 1 ) * W ) + y )) ” 
  &&  “ ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= ((x * W ) + (y - 1 ) )) ” 
  &&  “ (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (N >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (y <= m_pre) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (1 <= y) ” 
  &&  “ (y <= (m_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre x y kl dl ) ”
  &&  (((D + (((x * W ) + (y - 1 ) ) * sizeof(INT64)))) # Int64  |-> (Znth ((x * W ) + (y - 1 ) ) dl 0))
  **  (Int64Array.missing_i D ((x * W ) + (y - 1 ) ) 0 ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
.

Definition solver_partial_solve_wit_23 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
|--
  “ (x <= ((x + y ) - 1 )) ” 
  &&  “ (x >= 0) ” 
  &&  “ (y <= ((x + y ) - 1 )) ” 
  &&  “ (y >= 0) ” 
  &&  “ (x <= y) ” 
  &&  “ (0 <= ((x * W ) + y )) ” 
  &&  “ (((x * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= (((x - 1 ) * W ) + y )) ” 
  &&  “ ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= ((x * W ) + (y - 1 ) )) ” 
  &&  “ (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (N >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (y <= m_pre) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (1 <= y) ” 
  &&  “ (y <= (m_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre x y kl dl ) ”
  &&  (((fac + (((x + y ) - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth ((x + y ) - 1 ) fl 0))
  **  (Int64Array.missing_i fac ((x + y ) - 1 ) 0 (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
.

Definition solver_partial_solve_wit_24 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
|--
  “ (x <= ((x + y ) - 1 )) ” 
  &&  “ (x >= 0) ” 
  &&  “ (y <= ((x + y ) - 1 )) ” 
  &&  “ (y >= 0) ” 
  &&  “ (x <= y) ” 
  &&  “ (0 <= ((x * W ) + y )) ” 
  &&  “ (((x * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= (((x - 1 ) * W ) + y )) ” 
  &&  “ ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= ((x * W ) + (y - 1 ) )) ” 
  &&  “ (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (N >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (y <= m_pre) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (1 <= y) ” 
  &&  “ (y <= (m_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre x y kl dl ) ”
  &&  (((ifac + (x * sizeof(INT64)))) # Int64  |-> (Znth x il 0))
  **  (Int64Array.missing_i ifac x 0 (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
.

Definition solver_partial_solve_wit_25 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
|--
  “ (x <= ((x + y ) - 1 )) ” 
  &&  “ (x >= 0) ” 
  &&  “ (y <= ((x + y ) - 1 )) ” 
  &&  “ (y >= 0) ” 
  &&  “ (x <= y) ” 
  &&  “ (0 <= ((x * W ) + y )) ” 
  &&  “ (((x * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= (((x - 1 ) * W ) + y )) ” 
  &&  “ ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= ((x * W ) + (y - 1 ) )) ” 
  &&  “ (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (N >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (y <= m_pre) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (1 <= y) ” 
  &&  “ (y <= (m_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre x y kl dl ) ”
  &&  (((ifac + ((((x + y ) - 1 ) - x ) * sizeof(INT64)))) # Int64  |-> (Znth (((x + y ) - 1 ) - x ) il 0))
  **  (Int64Array.missing_i ifac (((x + y ) - 1 ) - x ) 0 (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
.

Definition solver_partial_solve_wit_26 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
|--
  “ (x <= ((x + y ) - 1 )) ” 
  &&  “ (x >= 0) ” 
  &&  “ (y <= ((x + y ) - 1 )) ” 
  &&  “ (y >= 0) ” 
  &&  “ (x <= y) ” 
  &&  “ (0 <= ((x * W ) + y )) ” 
  &&  “ (((x * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= (((x - 1 ) * W ) + y )) ” 
  &&  “ ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= ((x * W ) + (y - 1 ) )) ” 
  &&  “ (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (N >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (y <= m_pre) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (1 <= y) ” 
  &&  “ (y <= (m_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre x y kl dl ) ”
  &&  (((K + (((x * W ) + (y - 1 ) ) * sizeof(INT64)))) # Int64  |-> (Znth ((x * W ) + (y - 1 ) ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) 0))
  **  (Int64Array.missing_i K ((x * W ) + (y - 1 ) ) 0 ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
.

Definition solver_partial_solve_wit_27 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (y <= ((x + y ) - 1 )) ” 
  &&  “ (y >= 0) ” 
  &&  “ (x > y) ” 
  &&  “ (0 <= ((x * W ) + y )) ” 
  &&  “ (((x * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= (((x - 1 ) * W ) + y )) ” 
  &&  “ ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= ((x * W ) + (y - 1 ) )) ” 
  &&  “ (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (N >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (y <= m_pre) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (1 <= y) ” 
  &&  “ (y <= (m_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre x y kl dl ) ”
  &&  (((fac + (((x + y ) - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth ((x + y ) - 1 ) fl 0))
  **  (Int64Array.missing_i fac ((x + y ) - 1 ) 0 (N + 1 ) fl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
.

Definition solver_partial_solve_wit_28 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (y <= ((x + y ) - 1 )) ” 
  &&  “ (y >= 0) ” 
  &&  “ (x > y) ” 
  &&  “ (0 <= ((x * W ) + y )) ” 
  &&  “ (((x * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= (((x - 1 ) * W ) + y )) ” 
  &&  “ ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= ((x * W ) + (y - 1 ) )) ” 
  &&  “ (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (N >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (y <= m_pre) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (1 <= y) ” 
  &&  “ (y <= (m_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre x y kl dl ) ”
  &&  (((ifac + (y * sizeof(INT64)))) # Int64  |-> (Znth y il 0))
  **  (Int64Array.missing_i ifac y 0 (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
.

Definition solver_partial_solve_wit_29 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (y <= ((x + y ) - 1 )) ” 
  &&  “ (y >= 0) ” 
  &&  “ (x > y) ” 
  &&  “ (0 <= ((x * W ) + y )) ” 
  &&  “ (((x * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= (((x - 1 ) * W ) + y )) ” 
  &&  “ ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= ((x * W ) + (y - 1 ) )) ” 
  &&  “ (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (N >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (y <= m_pre) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (1 <= y) ” 
  &&  “ (y <= (m_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre x y kl dl ) ”
  &&  (((ifac + ((((x + y ) - 1 ) - y ) * sizeof(INT64)))) # Int64  |-> (Znth (((x + y ) - 1 ) - y ) il 0))
  **  (Int64Array.missing_i ifac (((x + y ) - 1 ) - y ) 0 (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
.

Definition solver_partial_solve_wit_30 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (y <= ((x + y ) - 1 )) ” 
  &&  “ (y >= 0) ” 
  &&  “ (x > y) ” 
  &&  “ (0 <= ((x * W ) + y )) ” 
  &&  “ (((x * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= (((x - 1 ) * W ) + y )) ” 
  &&  “ ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= ((x * W ) + (y - 1 ) )) ” 
  &&  “ (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (N >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (y <= m_pre) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (1 <= y) ” 
  &&  “ (y <= (m_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre x y kl dl ) ”
  &&  (((D + ((((x - 1 ) * W ) + y ) * sizeof(INT64)))) # Int64  |-> (Znth (((x - 1 ) * W ) + y ) dl 0))
  **  (Int64Array.missing_i D (((x - 1 ) * W ) + y ) 0 ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
.

Definition solver_partial_solve_wit_31 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (y <= ((x + y ) - 1 ))) (PreH2 : (y >= 0)) (PreH3 : (x > y)) (PreH4 : (0 <= ((x * W ) + y ))) (PreH5 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH6 : (0 <= (((x - 1 ) * W ) + y ))) (PreH7 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH9 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH10 : (N <= INT_MAX)) (PreH11 : (m_pre <= INT_MAX)) (PreH12 : (N >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (y <= m_pre)) (PreH15 : (N = (n_pre + m_pre ))) (PreH16 : (W = (m_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 2000)) (PreH19 : (0 <= m_pre)) (PreH20 : (m_pre <= 2000)) (PreH21 : ((Zlength (fl)) = (N + 1 ))) (PreH22 : ((Zlength (il)) = (N + 1 ))) (PreH23 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH24 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH25 : (P080Factorials fl (N + 1 ) )) (PreH26 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH28 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH29 : (1 <= x)) (PreH30 : (x <= n_pre)) (PreH31 : (1 <= y)) (PreH32 : (y <= (m_pre + 1 ))) (PreH33 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
|--
  “ (y <= ((x + y ) - 1 )) ” 
  &&  “ (y >= 0) ” 
  &&  “ (x > y) ” 
  &&  “ (0 <= ((x * W ) + y )) ” 
  &&  “ (((x * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= (((x - 1 ) * W ) + y )) ” 
  &&  “ ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= ((x * W ) + (y - 1 ) )) ” 
  &&  “ (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (N >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (y <= m_pre) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (1 <= y) ” 
  &&  “ (y <= (m_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre x y kl dl ) ”
  &&  (((D + (((x * W ) + (y - 1 ) ) * sizeof(INT64)))) # Int64  |-> (Znth ((x * W ) + (y - 1 ) ) dl 0))
  **  (Int64Array.missing_i D ((x * W ) + (y - 1 ) ) 0 ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
.

Definition solver_partial_solve_wit_32 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
|--
  “ (x <= ((x + y ) - 1 )) ” 
  &&  “ (x >= 0) ” 
  &&  “ (y <= ((x + y ) - 1 )) ” 
  &&  “ (y >= 0) ” 
  &&  “ (x > y) ” 
  &&  “ (0 <= ((x * W ) + y )) ” 
  &&  “ (((x * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= (((x - 1 ) * W ) + y )) ” 
  &&  “ ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= ((x * W ) + (y - 1 ) )) ” 
  &&  “ (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (N >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (y <= m_pre) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (1 <= y) ” 
  &&  “ (y <= (m_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre x y kl dl ) ”
  &&  (((fac + (((x + y ) - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth ((x + y ) - 1 ) fl 0))
  **  (Int64Array.missing_i fac ((x + y ) - 1 ) 0 (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
.

Definition solver_partial_solve_wit_33 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
|--
  “ (x <= ((x + y ) - 1 )) ” 
  &&  “ (x >= 0) ” 
  &&  “ (y <= ((x + y ) - 1 )) ” 
  &&  “ (y >= 0) ” 
  &&  “ (x > y) ” 
  &&  “ (0 <= ((x * W ) + y )) ” 
  &&  “ (((x * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= (((x - 1 ) * W ) + y )) ” 
  &&  “ ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= ((x * W ) + (y - 1 ) )) ” 
  &&  “ (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (N >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (y <= m_pre) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (1 <= y) ” 
  &&  “ (y <= (m_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre x y kl dl ) ”
  &&  (((ifac + (x * sizeof(INT64)))) # Int64  |-> (Znth x il 0))
  **  (Int64Array.missing_i ifac x 0 (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
.

Definition solver_partial_solve_wit_34 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
|--
  “ (x <= ((x + y ) - 1 )) ” 
  &&  “ (x >= 0) ” 
  &&  “ (y <= ((x + y ) - 1 )) ” 
  &&  “ (y >= 0) ” 
  &&  “ (x > y) ” 
  &&  “ (0 <= ((x * W ) + y )) ” 
  &&  “ (((x * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= (((x - 1 ) * W ) + y )) ” 
  &&  “ ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= ((x * W ) + (y - 1 ) )) ” 
  &&  “ (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (N >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (y <= m_pre) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (1 <= y) ” 
  &&  “ (y <= (m_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre x y kl dl ) ”
  &&  (((ifac + ((((x + y ) - 1 ) - x ) * sizeof(INT64)))) # Int64  |-> (Znth (((x + y ) - 1 ) - x ) il 0))
  **  (Int64Array.missing_i ifac (((x + y ) - 1 ) - x ) 0 (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
.

Definition solver_partial_solve_wit_35 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
|--
  “ (x <= ((x + y ) - 1 )) ” 
  &&  “ (x >= 0) ” 
  &&  “ (y <= ((x + y ) - 1 )) ” 
  &&  “ (y >= 0) ” 
  &&  “ (x > y) ” 
  &&  “ (0 <= ((x * W ) + y )) ” 
  &&  “ (((x * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= (((x - 1 ) * W ) + y )) ” 
  &&  “ ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= ((x * W ) + (y - 1 ) )) ” 
  &&  “ (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (N >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (y <= m_pre) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (1 <= y) ” 
  &&  “ (y <= (m_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre x y kl dl ) ”
  &&  (((K + (((x * W ) + (y - 1 ) ) * sizeof(INT64)))) # Int64  |-> (Znth ((x * W ) + (y - 1 ) ) kl 0))
  **  (Int64Array.missing_i K ((x * W ) + (y - 1 ) ) 0 ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
.

Definition solver_partial_solve_wit_36 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x <= y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (x <= ((x + y ) - 1 )) ” 
  &&  “ (x >= 0) ” 
  &&  “ (y <= ((x + y ) - 1 )) ” 
  &&  “ (y >= 0) ” 
  &&  “ (x <= y) ” 
  &&  “ (0 <= ((x * W ) + y )) ” 
  &&  “ (((x * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= (((x - 1 ) * W ) + y )) ” 
  &&  “ ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= ((x * W ) + (y - 1 ) )) ” 
  &&  “ (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (N >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (y <= m_pre) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (1 <= y) ” 
  &&  “ (y <= (m_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre x y kl dl ) ”
  &&  (((D + (((x * W ) + y ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i D ((x * W ) + y ) 0 ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) (replace_Znth (((x * W ) + y )) ((((Znth (((x - 1 ) * W ) + y ) kl 0) + (Znth ((x * W ) + (y - 1 ) ) kl 0) ) % ( 998244853 ) )) (kl)) )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
.

Definition solver_partial_solve_wit_37 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (y: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (x <= ((x + y ) - 1 ))) (PreH2 : (x >= 0)) (PreH3 : (y <= ((x + y ) - 1 ))) (PreH4 : (y >= 0)) (PreH5 : (x > y)) (PreH6 : (0 <= ((x * W ) + y ))) (PreH7 : (((x * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH8 : (0 <= (((x - 1 ) * W ) + y ))) (PreH9 : ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W ))) (PreH10 : (0 <= ((x * W ) + (y - 1 ) ))) (PreH11 : (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W ))) (PreH12 : (N <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (N >= INT_MIN)) (PreH15 : (m_pre >= INT_MIN)) (PreH16 : (y <= m_pre)) (PreH17 : (N = (n_pre + m_pre ))) (PreH18 : (W = (m_pre + 1 ))) (PreH19 : (0 <= n_pre)) (PreH20 : (n_pre <= 2000)) (PreH21 : (0 <= m_pre)) (PreH22 : (m_pre <= 2000)) (PreH23 : ((Zlength (fl)) = (N + 1 ))) (PreH24 : ((Zlength (il)) = (N + 1 ))) (PreH25 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH26 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH27 : (P080Factorials fl (N + 1 ) )) (PreH28 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH31 : (1 <= x)) (PreH32 : (x <= n_pre)) (PreH33 : (1 <= y)) (PreH34 : (y <= (m_pre + 1 ))) (PreH35 : (P080Tables n_pre m_pre x y kl dl )) ,
  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (x <= ((x + y ) - 1 )) ” 
  &&  “ (x >= 0) ” 
  &&  “ (y <= ((x + y ) - 1 )) ” 
  &&  “ (y >= 0) ” 
  &&  “ (x > y) ” 
  &&  “ (0 <= ((x * W ) + y )) ” 
  &&  “ (((x * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= (((x - 1 ) * W ) + y )) ” 
  &&  “ ((((x - 1 ) * W ) + y ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (0 <= ((x * W ) + (y - 1 ) )) ” 
  &&  “ (((x * W ) + (y - 1 ) ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (N >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (y <= m_pre) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= n_pre) ” 
  &&  “ (1 <= y) ” 
  &&  “ (y <= (m_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre x y kl dl ) ”
  &&  (((D + (((x * W ) + y ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i D ((x * W ) + y ) 0 ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full fac (N + 1 ) fl )
.

Definition solver_partial_solve_wit_38 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (0 <= ((n_pre * W ) + m_pre ))) (PreH2 : (((n_pre * W ) + m_pre ) < ((n_pre + 1 ) * W ))) (PreH3 : (N <= INT_MAX)) (PreH4 : (N >= INT_MIN)) (PreH5 : (x > n_pre)) (PreH6 : (N = (n_pre + m_pre ))) (PreH7 : (W = (m_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : (0 <= m_pre)) (PreH11 : (m_pre <= 2000)) (PreH12 : ((Zlength (fl)) = (N + 1 ))) (PreH13 : ((Zlength (il)) = (N + 1 ))) (PreH14 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH15 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH16 : (P080Factorials fl (N + 1 ) )) (PreH17 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH18 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH19 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH20 : (1 <= x)) (PreH21 : (x <= (n_pre + 1 ))) (PreH22 : (P080Tables n_pre m_pre x 0 kl dl )) ,
  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (0 <= ((n_pre * W ) + m_pre )) ” 
  &&  “ (((n_pre * W ) + m_pre ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (N >= INT_MIN) ” 
  &&  “ (x > n_pre) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= (n_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre x 0 kl dl ) ”
  &&  (((D + (((n_pre * W ) + m_pre ) * sizeof(INT64)))) # Int64  |-> (Znth ((n_pre * W ) + m_pre ) dl 0))
  **  (Int64Array.missing_i D ((n_pre * W ) + m_pre ) 0 ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
.

Definition solver_partial_solve_wit_39 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (fac: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (0 <= ((n_pre * W ) + m_pre ))) (PreH2 : (((n_pre * W ) + m_pre ) < ((n_pre + 1 ) * W ))) (PreH3 : (N <= INT_MAX)) (PreH4 : (N >= INT_MIN)) (PreH5 : (x > n_pre)) (PreH6 : (N = (n_pre + m_pre ))) (PreH7 : (W = (m_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : (0 <= m_pre)) (PreH11 : (m_pre <= 2000)) (PreH12 : ((Zlength (fl)) = (N + 1 ))) (PreH13 : ((Zlength (il)) = (N + 1 ))) (PreH14 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH15 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH16 : (P080Factorials fl (N + 1 ) )) (PreH17 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH18 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH19 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH20 : (1 <= x)) (PreH21 : (x <= (n_pre + 1 ))) (PreH22 : (P080Tables n_pre m_pre x 0 kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full fac (N + 1 ) fl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
|--
  “ (0 <= ((n_pre * W ) + m_pre )) ” 
  &&  “ (((n_pre * W ) + m_pre ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (N >= INT_MIN) ” 
  &&  “ (x > n_pre) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= (n_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre x 0 kl dl ) ”
  &&  (Int64Array.full fac ((n_pre + m_pre ) + 1 ) fl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
.

Definition solver_partial_solve_wit_40 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (ifac: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (0 <= ((n_pre * W ) + m_pre ))) (PreH2 : (((n_pre * W ) + m_pre ) < ((n_pre + 1 ) * W ))) (PreH3 : (N <= INT_MAX)) (PreH4 : (N >= INT_MIN)) (PreH5 : (x > n_pre)) (PreH6 : (N = (n_pre + m_pre ))) (PreH7 : (W = (m_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : (0 <= m_pre)) (PreH11 : (m_pre <= 2000)) (PreH12 : ((Zlength (fl)) = (N + 1 ))) (PreH13 : ((Zlength (il)) = (N + 1 ))) (PreH14 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH15 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH16 : (P080Factorials fl (N + 1 ) )) (PreH17 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH18 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH19 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH20 : (1 <= x)) (PreH21 : (x <= (n_pre + 1 ))) (PreH22 : (P080Tables n_pre m_pre x 0 kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full ifac (N + 1 ) il )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
|--
  “ (0 <= ((n_pre * W ) + m_pre )) ” 
  &&  “ (((n_pre * W ) + m_pre ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (N >= INT_MIN) ” 
  &&  “ (x > n_pre) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= (n_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre x 0 kl dl ) ”
  &&  (Int64Array.full ifac ((n_pre + m_pre ) + 1 ) il )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
.

Definition solver_partial_solve_wit_41 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (K: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (0 <= ((n_pre * W ) + m_pre ))) (PreH2 : (((n_pre * W ) + m_pre ) < ((n_pre + 1 ) * W ))) (PreH3 : (N <= INT_MAX)) (PreH4 : (N >= INT_MIN)) (PreH5 : (x > n_pre)) (PreH6 : (N = (n_pre + m_pre ))) (PreH7 : (W = (m_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : (0 <= m_pre)) (PreH11 : (m_pre <= 2000)) (PreH12 : ((Zlength (fl)) = (N + 1 ))) (PreH13 : ((Zlength (il)) = (N + 1 ))) (PreH14 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH15 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH16 : (P080Factorials fl (N + 1 ) )) (PreH17 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH18 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH19 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH20 : (1 <= x)) (PreH21 : (x <= (n_pre + 1 ))) (PreH22 : (P080Tables n_pre m_pre x 0 kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
  **  (Int64Array.full K ((n_pre + 1 ) * W ) kl )
|--
  “ (0 <= ((n_pre * W ) + m_pre )) ” 
  &&  “ (((n_pre * W ) + m_pre ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (N >= INT_MIN) ” 
  &&  “ (x > n_pre) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= (n_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre x 0 kl dl ) ”
  &&  (Int64Array.full K ((n_pre + 1 ) * (m_pre + 1 ) ) kl )
  **  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
.

Definition solver_partial_solve_wit_42 := 
forall (m_pre: Z) (n_pre: Z) (D: Z) (x: Z) (dl: (@list Z)) (kl: (@list Z)) (il: (@list Z)) (fl: (@list Z)) (W: Z) (N: Z) (PreH1 : (0 <= ((n_pre * W ) + m_pre ))) (PreH2 : (((n_pre * W ) + m_pre ) < ((n_pre + 1 ) * W ))) (PreH3 : (N <= INT_MAX)) (PreH4 : (N >= INT_MIN)) (PreH5 : (x > n_pre)) (PreH6 : (N = (n_pre + m_pre ))) (PreH7 : (W = (m_pre + 1 ))) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 2000)) (PreH10 : (0 <= m_pre)) (PreH11 : (m_pre <= 2000)) (PreH12 : ((Zlength (fl)) = (N + 1 ))) (PreH13 : ((Zlength (il)) = (N + 1 ))) (PreH14 : ((Zlength (kl)) = ((n_pre + 1 ) * W ))) (PreH15 : ((Zlength (dl)) = ((n_pre + 1 ) * W ))) (PreH16 : (P080Factorials fl (N + 1 ) )) (PreH17 : (P080InverseFactorials il 0 (N + 1 ) )) (PreH18 : forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853)))) (PreH19 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853)))) (PreH20 : (1 <= x)) (PreH21 : (x <= (n_pre + 1 ))) (PreH22 : (P080Tables n_pre m_pre x 0 kl dl )) ,
  (Int64Array.full D ((n_pre + 1 ) * W ) dl )
|--
  “ (0 <= ((n_pre * W ) + m_pre )) ” 
  &&  “ (((n_pre * W ) + m_pre ) < ((n_pre + 1 ) * W )) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (N >= INT_MIN) ” 
  &&  “ (x > n_pre) ” 
  &&  “ (N = (n_pre + m_pre )) ” 
  &&  “ (W = (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 2000) ” 
  &&  “ ((Zlength (fl)) = (N + 1 )) ” 
  &&  “ ((Zlength (il)) = (N + 1 )) ” 
  &&  “ ((Zlength (kl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ ((Zlength (dl)) = ((n_pre + 1 ) * W )) ” 
  &&  “ (P080Factorials fl (N + 1 ) ) ” 
  &&  “ (P080InverseFactorials il 0 (N + 1 ) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (N + 1 ))) -> ((((0 <= (Znth (j) (fl) (0))) /\ ((Znth (j) (fl) (0)) < 998244853)) /\ (0 <= (Znth (j) (il) (0)))) /\ ((Znth (j) (il) (0)) < 998244853))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < ((n_pre + 1 ) * W ))) -> ((((0 <= (Znth (j_2) (kl) (0))) /\ ((Znth (j_2) (kl) (0)) < 998244853)) /\ (0 <= (Znth (j_2) (dl) (0)))) /\ ((Znth (j_2) (dl) (0)) < 998244853))) ” 
  &&  “ (1 <= x) ” 
  &&  “ (x <= (n_pre + 1 )) ” 
  &&  “ (P080Tables n_pre m_pre x 0 kl dl ) ”
  &&  (Int64Array.full D ((n_pre + 1 ) * (m_pre + 1 ) ) dl )
.

Module Type VC_Correct.


Axiom proof_of_modpow_safety_wit_1 : modpow_safety_wit_1.
Axiom proof_of_modpow_safety_wit_2 : modpow_safety_wit_2.
Axiom proof_of_modpow_safety_wit_3 : modpow_safety_wit_3.
Axiom proof_of_modpow_safety_wit_4 : modpow_safety_wit_4.
Axiom proof_of_modpow_safety_wit_5 : modpow_safety_wit_5.
Axiom proof_of_modpow_safety_wit_6 : modpow_safety_wit_6.
Axiom proof_of_modpow_safety_wit_7 : modpow_safety_wit_7.
Axiom proof_of_modpow_safety_wit_8 : modpow_safety_wit_8.
Axiom proof_of_modpow_safety_wit_9 : modpow_safety_wit_9.
Axiom proof_of_modpow_safety_wit_10 : modpow_safety_wit_10.
Axiom proof_of_modpow_safety_wit_11 : modpow_safety_wit_11.
Axiom proof_of_modpow_safety_wit_12 : modpow_safety_wit_12.
Axiom proof_of_modpow_safety_wit_13 : modpow_safety_wit_13.
Axiom proof_of_modpow_safety_wit_14 : modpow_safety_wit_14.
Axiom proof_of_modpow_safety_wit_15 : modpow_safety_wit_15.
Axiom proof_of_modpow_entail_wit_1 : modpow_entail_wit_1.
Axiom proof_of_modpow_entail_wit_2_1 : modpow_entail_wit_2_1.
Axiom proof_of_modpow_entail_wit_2_2 : modpow_entail_wit_2_2.
Axiom proof_of_modpow_return_wit_1 : modpow_return_wit_1.
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
Axiom proof_of_solver_safety_wit_50 : solver_safety_wit_50.
Axiom proof_of_solver_safety_wit_51 : solver_safety_wit_51.
Axiom proof_of_solver_safety_wit_52 : solver_safety_wit_52.
Axiom proof_of_solver_safety_wit_53 : solver_safety_wit_53.
Axiom proof_of_solver_safety_wit_54 : solver_safety_wit_54.
Axiom proof_of_solver_safety_wit_55 : solver_safety_wit_55.
Axiom proof_of_solver_safety_wit_56 : solver_safety_wit_56.
Axiom proof_of_solver_safety_wit_57 : solver_safety_wit_57.
Axiom proof_of_solver_safety_wit_58 : solver_safety_wit_58.
Axiom proof_of_solver_safety_wit_59 : solver_safety_wit_59.
Axiom proof_of_solver_safety_wit_60 : solver_safety_wit_60.
Axiom proof_of_solver_safety_wit_61 : solver_safety_wit_61.
Axiom proof_of_solver_safety_wit_62 : solver_safety_wit_62.
Axiom proof_of_solver_safety_wit_63 : solver_safety_wit_63.
Axiom proof_of_solver_safety_wit_64 : solver_safety_wit_64.
Axiom proof_of_solver_safety_wit_65 : solver_safety_wit_65.
Axiom proof_of_solver_safety_wit_66 : solver_safety_wit_66.
Axiom proof_of_solver_safety_wit_67 : solver_safety_wit_67.
Axiom proof_of_solver_safety_wit_68 : solver_safety_wit_68.
Axiom proof_of_solver_safety_wit_69 : solver_safety_wit_69.
Axiom proof_of_solver_safety_wit_70 : solver_safety_wit_70.
Axiom proof_of_solver_safety_wit_71 : solver_safety_wit_71.
Axiom proof_of_solver_safety_wit_72 : solver_safety_wit_72.
Axiom proof_of_solver_safety_wit_73 : solver_safety_wit_73.
Axiom proof_of_solver_safety_wit_74 : solver_safety_wit_74.
Axiom proof_of_solver_safety_wit_75 : solver_safety_wit_75.
Axiom proof_of_solver_safety_wit_76 : solver_safety_wit_76.
Axiom proof_of_solver_safety_wit_77 : solver_safety_wit_77.
Axiom proof_of_solver_safety_wit_78 : solver_safety_wit_78.
Axiom proof_of_solver_safety_wit_79 : solver_safety_wit_79.
Axiom proof_of_solver_safety_wit_80 : solver_safety_wit_80.
Axiom proof_of_solver_safety_wit_81 : solver_safety_wit_81.
Axiom proof_of_solver_safety_wit_82 : solver_safety_wit_82.
Axiom proof_of_solver_safety_wit_83 : solver_safety_wit_83.
Axiom proof_of_solver_safety_wit_84 : solver_safety_wit_84.
Axiom proof_of_solver_safety_wit_85 : solver_safety_wit_85.
Axiom proof_of_solver_safety_wit_86 : solver_safety_wit_86.
Axiom proof_of_solver_safety_wit_87 : solver_safety_wit_87.
Axiom proof_of_solver_safety_wit_88 : solver_safety_wit_88.
Axiom proof_of_solver_safety_wit_89 : solver_safety_wit_89.
Axiom proof_of_solver_safety_wit_90 : solver_safety_wit_90.
Axiom proof_of_solver_safety_wit_91 : solver_safety_wit_91.
Axiom proof_of_solver_safety_wit_92 : solver_safety_wit_92.
Axiom proof_of_solver_safety_wit_93 : solver_safety_wit_93.
Axiom proof_of_solver_safety_wit_94 : solver_safety_wit_94.
Axiom proof_of_solver_safety_wit_95 : solver_safety_wit_95.
Axiom proof_of_solver_safety_wit_96 : solver_safety_wit_96.
Axiom proof_of_solver_safety_wit_97 : solver_safety_wit_97.
Axiom proof_of_solver_safety_wit_98 : solver_safety_wit_98.
Axiom proof_of_solver_safety_wit_99 : solver_safety_wit_99.
Axiom proof_of_solver_safety_wit_100 : solver_safety_wit_100.
Axiom proof_of_solver_safety_wit_101 : solver_safety_wit_101.
Axiom proof_of_solver_safety_wit_102 : solver_safety_wit_102.
Axiom proof_of_solver_safety_wit_103 : solver_safety_wit_103.
Axiom proof_of_solver_safety_wit_104 : solver_safety_wit_104.
Axiom proof_of_solver_safety_wit_105 : solver_safety_wit_105.
Axiom proof_of_solver_safety_wit_106 : solver_safety_wit_106.
Axiom proof_of_solver_safety_wit_107 : solver_safety_wit_107.
Axiom proof_of_solver_safety_wit_108 : solver_safety_wit_108.
Axiom proof_of_solver_safety_wit_109 : solver_safety_wit_109.
Axiom proof_of_solver_safety_wit_110 : solver_safety_wit_110.
Axiom proof_of_solver_safety_wit_111 : solver_safety_wit_111.
Axiom proof_of_solver_safety_wit_112 : solver_safety_wit_112.
Axiom proof_of_solver_safety_wit_113 : solver_safety_wit_113.
Axiom proof_of_solver_safety_wit_114 : solver_safety_wit_114.
Axiom proof_of_solver_safety_wit_115 : solver_safety_wit_115.
Axiom proof_of_solver_safety_wit_116 : solver_safety_wit_116.
Axiom proof_of_solver_safety_wit_117 : solver_safety_wit_117.
Axiom proof_of_solver_safety_wit_118 : solver_safety_wit_118.
Axiom proof_of_solver_safety_wit_119 : solver_safety_wit_119.
Axiom proof_of_solver_safety_wit_120 : solver_safety_wit_120.
Axiom proof_of_solver_safety_wit_121 : solver_safety_wit_121.
Axiom proof_of_solver_safety_wit_122 : solver_safety_wit_122.
Axiom proof_of_solver_safety_wit_123 : solver_safety_wit_123.
Axiom proof_of_solver_safety_wit_124 : solver_safety_wit_124.
Axiom proof_of_solver_safety_wit_125 : solver_safety_wit_125.
Axiom proof_of_solver_safety_wit_126 : solver_safety_wit_126.
Axiom proof_of_solver_safety_wit_127 : solver_safety_wit_127.
Axiom proof_of_solver_safety_wit_128 : solver_safety_wit_128.
Axiom proof_of_solver_safety_wit_129 : solver_safety_wit_129.
Axiom proof_of_solver_safety_wit_130 : solver_safety_wit_130.
Axiom proof_of_solver_safety_wit_131 : solver_safety_wit_131.
Axiom proof_of_solver_safety_wit_132 : solver_safety_wit_132.
Axiom proof_of_solver_safety_wit_133 : solver_safety_wit_133.
Axiom proof_of_solver_safety_wit_134 : solver_safety_wit_134.
Axiom proof_of_solver_safety_wit_135 : solver_safety_wit_135.
Axiom proof_of_solver_safety_wit_136 : solver_safety_wit_136.
Axiom proof_of_solver_safety_wit_137 : solver_safety_wit_137.
Axiom proof_of_solver_safety_wit_138 : solver_safety_wit_138.
Axiom proof_of_solver_safety_wit_139 : solver_safety_wit_139.
Axiom proof_of_solver_safety_wit_140 : solver_safety_wit_140.
Axiom proof_of_solver_safety_wit_141 : solver_safety_wit_141.
Axiom proof_of_solver_safety_wit_142 : solver_safety_wit_142.
Axiom proof_of_solver_safety_wit_143 : solver_safety_wit_143.
Axiom proof_of_solver_safety_wit_144 : solver_safety_wit_144.
Axiom proof_of_solver_safety_wit_145 : solver_safety_wit_145.
Axiom proof_of_solver_safety_wit_146 : solver_safety_wit_146.
Axiom proof_of_solver_safety_wit_147 : solver_safety_wit_147.
Axiom proof_of_solver_safety_wit_148 : solver_safety_wit_148.
Axiom proof_of_solver_safety_wit_149 : solver_safety_wit_149.
Axiom proof_of_solver_safety_wit_150 : solver_safety_wit_150.
Axiom proof_of_solver_safety_wit_151 : solver_safety_wit_151.
Axiom proof_of_solver_safety_wit_152 : solver_safety_wit_152.
Axiom proof_of_solver_safety_wit_153 : solver_safety_wit_153.
Axiom proof_of_solver_safety_wit_154 : solver_safety_wit_154.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Axiom proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Axiom proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Axiom proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Axiom proof_of_solver_entail_wit_11_1 : solver_entail_wit_11_1.
Axiom proof_of_solver_entail_wit_11_2 : solver_entail_wit_11_2.
Axiom proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Axiom proof_of_solver_entail_wit_13 : solver_entail_wit_13.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7_pure : solver_partial_solve_wit_7_pure.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.
Axiom proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8.
Axiom proof_of_solver_partial_solve_wit_9 : solver_partial_solve_wit_9.
Axiom proof_of_solver_partial_solve_wit_10 : solver_partial_solve_wit_10.
Axiom proof_of_solver_partial_solve_wit_11_pure : solver_partial_solve_wit_11_pure.
Axiom proof_of_solver_partial_solve_wit_11 : solver_partial_solve_wit_11.
Axiom proof_of_solver_partial_solve_wit_12_pure : solver_partial_solve_wit_12_pure.
Axiom proof_of_solver_partial_solve_wit_12 : solver_partial_solve_wit_12.
Axiom proof_of_solver_partial_solve_wit_13 : solver_partial_solve_wit_13.
Axiom proof_of_solver_partial_solve_wit_14 : solver_partial_solve_wit_14.
Axiom proof_of_solver_partial_solve_wit_15 : solver_partial_solve_wit_15.
Axiom proof_of_solver_partial_solve_wit_16 : solver_partial_solve_wit_16.
Axiom proof_of_solver_partial_solve_wit_17 : solver_partial_solve_wit_17.
Axiom proof_of_solver_partial_solve_wit_18 : solver_partial_solve_wit_18.
Axiom proof_of_solver_partial_solve_wit_19 : solver_partial_solve_wit_19.
Axiom proof_of_solver_partial_solve_wit_20 : solver_partial_solve_wit_20.
Axiom proof_of_solver_partial_solve_wit_21 : solver_partial_solve_wit_21.
Axiom proof_of_solver_partial_solve_wit_22 : solver_partial_solve_wit_22.
Axiom proof_of_solver_partial_solve_wit_23 : solver_partial_solve_wit_23.
Axiom proof_of_solver_partial_solve_wit_24 : solver_partial_solve_wit_24.
Axiom proof_of_solver_partial_solve_wit_25 : solver_partial_solve_wit_25.
Axiom proof_of_solver_partial_solve_wit_26 : solver_partial_solve_wit_26.
Axiom proof_of_solver_partial_solve_wit_27 : solver_partial_solve_wit_27.
Axiom proof_of_solver_partial_solve_wit_28 : solver_partial_solve_wit_28.
Axiom proof_of_solver_partial_solve_wit_29 : solver_partial_solve_wit_29.
Axiom proof_of_solver_partial_solve_wit_30 : solver_partial_solve_wit_30.
Axiom proof_of_solver_partial_solve_wit_31 : solver_partial_solve_wit_31.
Axiom proof_of_solver_partial_solve_wit_32 : solver_partial_solve_wit_32.
Axiom proof_of_solver_partial_solve_wit_33 : solver_partial_solve_wit_33.
Axiom proof_of_solver_partial_solve_wit_34 : solver_partial_solve_wit_34.
Axiom proof_of_solver_partial_solve_wit_35 : solver_partial_solve_wit_35.
Axiom proof_of_solver_partial_solve_wit_36 : solver_partial_solve_wit_36.
Axiom proof_of_solver_partial_solve_wit_37 : solver_partial_solve_wit_37.
Axiom proof_of_solver_partial_solve_wit_38 : solver_partial_solve_wit_38.
Axiom proof_of_solver_partial_solve_wit_39 : solver_partial_solve_wit_39.
Axiom proof_of_solver_partial_solve_wit_40 : solver_partial_solve_wit_40.
Axiom proof_of_solver_partial_solve_wit_41 : solver_partial_solve_wit_41.
Axiom proof_of_solver_partial_solve_wit_42 : solver_partial_solve_wit_42.

End VC_Correct.
