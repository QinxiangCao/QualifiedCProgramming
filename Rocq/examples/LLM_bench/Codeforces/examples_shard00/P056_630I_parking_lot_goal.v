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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P056_630I_parking_lot_lib.
Local Open Scope sac.

(*----- Function power4 -----*)

Definition power4_safety_wit_1 := 
forall (e_pre: Z) (PreH1 : ((-1) <= e_pre)) (PreH2 : (e_pre <= 27)) ,
  ((( &( "r" ) )) # Int64  |->_)
  **  ((( &( "e" ) )) # Int  |-> e_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition power4_safety_wit_2 := 
forall (e_pre: Z) (r: Z) (e: Z) (PreH1 : (e_pre = (-1))) (PreH2 : (e = (-1))) (PreH3 : (r = 1)) ,
  ((( &( "e" ) )) # Int  |-> e)
  **  ((( &( "r" ) )) # Int64  |-> r)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition power4_safety_wit_3 := 
forall (e_pre: Z) (r: Z) (e: Z) (PreH1 : (0 <= e)) (PreH2 : (e <= e_pre)) (PreH3 : (e_pre <= 27)) (PreH4 : (r = (Z.pow (4) ((e_pre - e ))))) (PreH5 : (1 <= r)) (PreH6 : (r <= (Z.pow (4) (27)))) (PreH7 : ((0 < e) -> (r <= (Z.pow (4) (26))))) ,
  ((( &( "e" ) )) # Int  |-> e)
  **  ((( &( "r" ) )) # Int64  |-> r)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition power4_safety_wit_4 := 
forall (e_pre: Z) (r: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (e_pre = (-1))) (PreH3 : (e = (-1))) (PreH4 : (r = 1)) ,
  ((( &( "e" ) )) # Int  |-> e)
  **  ((( &( "r" ) )) # Int64  |-> r)
|--
  “ False ”
.

Definition power4_safety_wit_5 := 
(
forall (e_pre: Z) (r: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= e_pre)) (PreH4 : (e_pre <= 27)) (PreH5 : (r = (Z.pow (4) ((e_pre - e ))))) (PreH6 : (1 <= r)) (PreH7 : (r <= (Z.pow (4) (27)))) (PreH8 : ((0 < e) -> (r <= (Z.pow (4) (26))))) ,
  ((( &( "e" ) )) # Int  |-> e)
  **  ((( &( "r" ) )) # Int64  |-> r)
|--
  “ ((r * 4 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (r * 4 )) ”
) \/
(
forall (e_pre: Z) (r: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= e_pre)) (PreH4 : (e_pre <= 27)) (PreH5 : (r = (Z.pow (4) ((e_pre - e ))))) (PreH6 : (1 <= r)) (PreH7 : (r <= (Z.pow (4) (27)))) (PreH8 : ((0 < e) -> (r <= (Z.pow (4) (26))))) ,
  ((( &( "e" ) )) # Int  |-> e)
  **  ((( &( "r" ) )) # Int64  |-> r)
|--
  “ ((r * 4 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (r * 4 )) ”
).

Definition power4_safety_wit_5_split_goal_1 := 
forall (e_pre: Z) (r: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= e_pre)) (PreH4 : (e_pre <= 27)) (PreH5 : (r = (Z.pow (4) ((e_pre - e ))))) (PreH6 : (1 <= r)) (PreH7 : (r <= (Z.pow (4) (27)))) (PreH8 : ((0 < e) -> (r <= (Z.pow (4) (26))))) ,
  ((( &( "e" ) )) # Int  |-> e)
  **  ((( &( "r" ) )) # Int64  |-> r)
|--
  “ ((r * 4 ) <= INT64_MAX) ”
.

Definition power4_safety_wit_5_split_goal_2 := 
forall (e_pre: Z) (r: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= e_pre)) (PreH4 : (e_pre <= 27)) (PreH5 : (r = (Z.pow (4) ((e_pre - e ))))) (PreH6 : (1 <= r)) (PreH7 : (r <= (Z.pow (4) (27)))) (PreH8 : ((0 < e) -> (r <= (Z.pow (4) (26))))) ,
  ((( &( "e" ) )) # Int  |-> e)
  **  ((( &( "r" ) )) # Int64  |-> r)
|--
  “ ((INT64_MIN) <= (r * 4 )) ”
.

Definition power4_safety_wit_6 := 
forall (e_pre: Z) (r: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= e_pre)) (PreH4 : (e_pre <= 27)) (PreH5 : (r = (Z.pow (4) ((e_pre - e ))))) (PreH6 : (1 <= r)) (PreH7 : (r <= (Z.pow (4) (27)))) (PreH8 : ((0 < e) -> (r <= (Z.pow (4) (26))))) ,
  ((( &( "e" ) )) # Int  |-> e)
  **  ((( &( "r" ) )) # Int64  |-> r)
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition power4_safety_wit_7 := 
forall (e_pre: Z) (r: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= e_pre)) (PreH4 : (e_pre <= 27)) (PreH5 : (r = (Z.pow (4) ((e_pre - e ))))) (PreH6 : (1 <= r)) (PreH7 : (r <= (Z.pow (4) (27)))) (PreH8 : ((0 < e) -> (r <= (Z.pow (4) (26))))) ,
  ((( &( "e" ) )) # Int  |-> e)
  **  ((( &( "r" ) )) # Int64  |-> (r * 4 ))
|--
  “ ((e - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (e - 1 )) ”
.

Definition power4_safety_wit_8 := 
forall (e_pre: Z) (r: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= e_pre)) (PreH4 : (e_pre <= 27)) (PreH5 : (r = (Z.pow (4) ((e_pre - e ))))) (PreH6 : (1 <= r)) (PreH7 : (r <= (Z.pow (4) (27)))) (PreH8 : ((0 < e) -> (r <= (Z.pow (4) (26))))) ,
  ((( &( "e" ) )) # Int  |-> e)
  **  ((( &( "r" ) )) # Int64  |-> (r * 4 ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition power4_entail_wit_1 := 
forall (e_pre: Z) (PreH1 : ((-1) <= e_pre)) (PreH2 : (e_pre <= 27)) ,
  TT && emp 
|--
  (“ (e_pre = (-1)) ” 
  &&  “ (e_pre = (-1)) ” 
  &&  “ (1 = 1) ”
  &&  emp)
  ||
  (“ (0 <= e_pre) ” 
  &&  “ (e_pre <= e_pre) ” 
  &&  “ (e_pre <= 27) ” 
  &&  “ (1 = (Z.pow (4) ((e_pre - e_pre )))) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (Z.pow (4) (27))) ” 
  &&  “ ((0 < e_pre) -> (1 <= (Z.pow (4) (26)))) ”
  &&  emp)
.

Definition power4_entail_wit_2 := 
(
forall (e_pre: Z) (r: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= e_pre)) (PreH4 : (e_pre <= 27)) (PreH5 : (r = (Z.pow (4) ((e_pre - e ))))) (PreH6 : (1 <= r)) (PreH7 : (r <= (Z.pow (4) (27)))) (PreH8 : ((0 < e) -> (r <= (Z.pow (4) (26))))) ,
  TT && emp 
|--
  “ (0 <= (e - 1 )) ” 
  &&  “ ((e - 1 ) <= e_pre) ” 
  &&  “ (e_pre <= 27) ” 
  &&  “ ((r * 4 ) = (Z.pow (4) ((e_pre - (e - 1 ) )))) ” 
  &&  “ (1 <= (r * 4 )) ” 
  &&  “ ((r * 4 ) <= (Z.pow (4) (27))) ” 
  &&  “ ((0 < (e - 1 )) -> ((r * 4 ) <= (Z.pow (4) (26)))) ”
  &&  emp
) \/
(
forall (e_pre: Z) (r: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= e_pre)) (PreH4 : (e_pre <= 27)) (PreH5 : (r = (Z.pow (4) ((e_pre - e ))))) (PreH6 : (1 <= r)) (PreH7 : (r <= (Z.pow (4) (27)))) (PreH8 : ((0 < e) -> (r <= (Z.pow (4) (26))))) ,
  TT && emp 
|--
  “ ((0 < (e - 1 )) -> ((r * 4 ) <= (Z.pow (4) (26)))) ” 
  &&  “ ((r * 4 ) <= (Z.pow (4) (27))) ” 
  &&  “ ((r * 4 ) = (Z.pow (4) ((e_pre - (e - 1 ) )))) ”
  &&  emp
).

Definition power4_entail_wit_2_split_goal_1 := 
forall (e_pre: Z) (r: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= e_pre)) (PreH4 : (e_pre <= 27)) (PreH5 : (r = (Z.pow (4) ((e_pre - e ))))) (PreH6 : (1 <= r)) (PreH7 : (r <= (Z.pow (4) (27)))) (PreH8 : ((0 < e) -> (r <= (Z.pow (4) (26))))) ,
  ((0 < (e - 1 )) -> ((r * 4 ) <= (Z.pow (4) (26))))
.

Definition power4_entail_wit_2_split_goal_2 := 
forall (e_pre: Z) (r: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= e_pre)) (PreH4 : (e_pre <= 27)) (PreH5 : (r = (Z.pow (4) ((e_pre - e ))))) (PreH6 : (1 <= r)) (PreH7 : (r <= (Z.pow (4) (27)))) (PreH8 : ((0 < e) -> (r <= (Z.pow (4) (26))))) ,
  ((r * 4 ) <= (Z.pow (4) (27)))
.

Definition power4_entail_wit_2_split_goal_3 := 
forall (e_pre: Z) (r: Z) (e: Z) (PreH1 : (e > 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= e_pre)) (PreH4 : (e_pre <= 27)) (PreH5 : (r = (Z.pow (4) ((e_pre - e ))))) (PreH6 : (1 <= r)) (PreH7 : (r <= (Z.pow (4) (27)))) (PreH8 : ((0 < e) -> (r <= (Z.pow (4) (26))))) ,
  ((r * 4 ) = (Z.pow (4) ((e_pre - (e - 1 ) ))))
.

Definition power4_return_wit_1 := 
forall (e_pre: Z) (r: Z) (e: Z) (PreH1 : (e <= 0)) (PreH2 : (e_pre = (-1))) (PreH3 : (e = (-1))) (PreH4 : (r = 1)) ,
  TT && emp 
|--
  “ (e_pre = (-1)) ” 
  &&  “ (r = 1) ”
  &&  emp
.

Definition power4_return_wit_2 := 
(
forall (e_pre: Z) (r: Z) (e: Z) (PreH1 : (e <= 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= e_pre)) (PreH4 : (e_pre <= 27)) (PreH5 : (r = (Z.pow (4) ((e_pre - e ))))) (PreH6 : (1 <= r)) (PreH7 : (r <= (Z.pow (4) (27)))) (PreH8 : ((0 < e) -> (r <= (Z.pow (4) (26))))) ,
  TT && emp 
|--
  “ (0 <= e_pre) ” 
  &&  “ (r = (Z.pow (4) (e_pre))) ”
  &&  emp
) \/
(
forall (e_pre: Z) (r: Z) (e: Z) (PreH1 : (e <= 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= e_pre)) (PreH4 : (e_pre <= 27)) (PreH5 : (r = (Z.pow (4) ((e_pre - e ))))) (PreH6 : (1 <= r)) (PreH7 : (r <= (Z.pow (4) (27)))) (PreH8 : ((0 < e) -> (r <= (Z.pow (4) (26))))) ,
  TT && emp 
|--
  “ (r = (Z.pow (4) (e_pre))) ”
  &&  emp
).

Definition power4_return_wit_2_split_goal_1 := 
forall (e_pre: Z) (r: Z) (e: Z) (PreH1 : (e <= 0)) (PreH2 : (0 <= e)) (PreH3 : (e <= e_pre)) (PreH4 : (e_pre <= 27)) (PreH5 : (r = (Z.pow (4) ((e_pre - e ))))) (PreH6 : (1 <= r)) (PreH7 : (r <= (Z.pow (4) (27)))) (PreH8 : ((0 < e) -> (r <= (Z.pow (4) (26))))) ,
  (r = (Z.pow (4) (e_pre)))
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (n_pre: Z) (PreH1 : (3 <= n_pre)) (PreH2 : (n_pre <= 30)) ,
  ((( &( "first" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((n_pre - 3 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 3 )) ”
.

Definition solver_safety_wit_2 := 
forall (n_pre: Z) (PreH1 : (3 <= n_pre)) (PreH2 : (n_pre <= 30)) ,
  ((( &( "first" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition solver_safety_wit_3 := 
forall (n_pre: Z) (retval: Z) (PreH1 : ((n_pre - 3 ) = (-1))) (PreH2 : (retval = 1)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 30)) ,
  ((( &( "first" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ False ”
.

Definition solver_safety_wit_4 := 
forall (n_pre: Z) (retval: Z) (PreH1 : (0 <= (n_pre - 3 ))) (PreH2 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 30)) ,
  ((( &( "second" ) )) # Int64  |->_)
  **  ((( &( "first" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((n_pre - 4 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 4 )) ”
.

Definition solver_safety_wit_5 := 
forall (n_pre: Z) (retval: Z) (PreH1 : (0 <= (n_pre - 3 ))) (PreH2 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 30)) ,
  ((( &( "second" ) )) # Int64  |->_)
  **  ((( &( "first" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition solver_safety_wit_6 := 
(
forall (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : ((n_pre - 4 ) = (-1))) (PreH2 : (retval_2 = 1)) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  ((( &( "second" ) )) # Int64  |-> retval_2)
  **  ((( &( "first" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (((24 * retval ) + (((n_pre - 3 ) * 36 ) * retval_2 ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((24 * retval ) + (((n_pre - 3 ) * 36 ) * retval_2 ) )) ”
) \/
(
forall (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : ((n_pre - 4 ) = (-1))) (PreH2 : (retval_2 = 1)) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  ((( &( "second" ) )) # Int64  |-> retval_2)
  **  ((( &( "first" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (((24 * retval ) + (((n_pre - 3 ) * 36 ) * retval_2 ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((24 * retval ) + (((n_pre - 3 ) * 36 ) * retval_2 ) )) ”
).

Definition solver_safety_wit_6_split_goal_1 := 
forall (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : ((n_pre - 4 ) = (-1))) (PreH2 : (retval_2 = 1)) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  ((( &( "second" ) )) # Int64  |-> retval_2)
  **  ((( &( "first" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (((24 * retval ) + (((n_pre - 3 ) * 36 ) * retval_2 ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_6_split_goal_2 := 
forall (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : ((n_pre - 4 ) = (-1))) (PreH2 : (retval_2 = 1)) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  ((( &( "second" ) )) # Int64  |-> retval_2)
  **  ((( &( "first" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((INT64_MIN) <= ((24 * retval ) + (((n_pre - 3 ) * 36 ) * retval_2 ) )) ”
.

Definition solver_safety_wit_7 := 
(
forall (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (n_pre - 4 ))) (PreH2 : (retval_2 = (Z.pow (4) ((n_pre - 4 ))))) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  ((( &( "second" ) )) # Int64  |-> retval_2)
  **  ((( &( "first" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (((24 * retval ) + (((n_pre - 3 ) * 36 ) * retval_2 ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((24 * retval ) + (((n_pre - 3 ) * 36 ) * retval_2 ) )) ”
) \/
(
forall (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (n_pre - 4 ))) (PreH2 : (retval_2 = (Z.pow (4) ((n_pre - 4 ))))) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  ((( &( "second" ) )) # Int64  |-> retval_2)
  **  ((( &( "first" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (((24 * retval ) + (((n_pre - 3 ) * 36 ) * retval_2 ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((24 * retval ) + (((n_pre - 3 ) * 36 ) * retval_2 ) )) ”
).

Definition solver_safety_wit_7_split_goal_1 := 
forall (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (n_pre - 4 ))) (PreH2 : (retval_2 = (Z.pow (4) ((n_pre - 4 ))))) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  ((( &( "second" ) )) # Int64  |-> retval_2)
  **  ((( &( "first" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (((24 * retval ) + (((n_pre - 3 ) * 36 ) * retval_2 ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_7_split_goal_2 := 
forall (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (n_pre - 4 ))) (PreH2 : (retval_2 = (Z.pow (4) ((n_pre - 4 ))))) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  ((( &( "second" ) )) # Int64  |-> retval_2)
  **  ((( &( "first" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((INT64_MIN) <= ((24 * retval ) + (((n_pre - 3 ) * 36 ) * retval_2 ) )) ”
.

Definition solver_safety_wit_8 := 
forall (n_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : ((n_pre - 4 ) = (-1))) (PreH2 : (retval = 1)) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval_2 = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  ((( &( "second" ) )) # Int64  |-> retval)
  **  ((( &( "first" ) )) # Int64  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((((n_pre - 3 ) * 36 ) * retval ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((n_pre - 3 ) * 36 ) * retval )) ”
.

Definition solver_safety_wit_9 := 
(
forall (n_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= (n_pre - 4 ))) (PreH2 : (retval = (Z.pow (4) ((n_pre - 4 ))))) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval_2 = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  ((( &( "second" ) )) # Int64  |-> retval)
  **  ((( &( "first" ) )) # Int64  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((((n_pre - 3 ) * 36 ) * retval ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((n_pre - 3 ) * 36 ) * retval )) ”
) \/
(
forall (n_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= (n_pre - 4 ))) (PreH2 : (retval = (Z.pow (4) ((n_pre - 4 ))))) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval_2 = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  ((( &( "second" ) )) # Int64  |-> retval)
  **  ((( &( "first" ) )) # Int64  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((((n_pre - 3 ) * 36 ) * retval ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((n_pre - 3 ) * 36 ) * retval )) ”
).

Definition solver_safety_wit_9_split_goal_1 := 
forall (n_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= (n_pre - 4 ))) (PreH2 : (retval = (Z.pow (4) ((n_pre - 4 ))))) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval_2 = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  ((( &( "second" ) )) # Int64  |-> retval)
  **  ((( &( "first" ) )) # Int64  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((((n_pre - 3 ) * 36 ) * retval ) <= INT64_MAX) ”
.

Definition solver_safety_wit_9_split_goal_2 := 
forall (n_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= (n_pre - 4 ))) (PreH2 : (retval = (Z.pow (4) ((n_pre - 4 ))))) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval_2 = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  ((( &( "second" ) )) # Int64  |-> retval)
  **  ((( &( "first" ) )) # Int64  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((INT64_MIN) <= (((n_pre - 3 ) * 36 ) * retval )) ”
.

Definition solver_safety_wit_10 := 
forall (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : ((n_pre - 4 ) = (-1))) (PreH2 : (retval_2 = 1)) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  ((( &( "second" ) )) # Int64  |-> retval_2)
  **  ((( &( "first" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (((n_pre - 3 ) * 36 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((n_pre - 3 ) * 36 )) ”
.

Definition solver_safety_wit_11 := 
forall (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (n_pre - 4 ))) (PreH2 : (retval_2 = (Z.pow (4) ((n_pre - 4 ))))) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  ((( &( "second" ) )) # Int64  |-> retval_2)
  **  ((( &( "first" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (((n_pre - 3 ) * 36 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((n_pre - 3 ) * 36 )) ”
.

Definition solver_safety_wit_12 := 
forall (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : ((n_pre - 4 ) = (-1))) (PreH2 : (retval_2 = 1)) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  ((( &( "second" ) )) # Int64  |-> retval_2)
  **  ((( &( "first" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((n_pre - 3 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 3 )) ”
.

Definition solver_safety_wit_13 := 
forall (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (n_pre - 4 ))) (PreH2 : (retval_2 = (Z.pow (4) ((n_pre - 4 ))))) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  ((( &( "second" ) )) # Int64  |-> retval_2)
  **  ((( &( "first" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((n_pre - 3 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 3 )) ”
.

Definition solver_safety_wit_14 := 
(
forall (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : ((n_pre - 4 ) = (-1))) (PreH2 : (retval_2 = 1)) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  ((( &( "second" ) )) # Int64  |-> retval_2)
  **  ((( &( "first" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((24 * retval ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (24 * retval )) ”
) \/
(
forall (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : ((n_pre - 4 ) = (-1))) (PreH2 : (retval_2 = 1)) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  ((( &( "second" ) )) # Int64  |-> retval_2)
  **  ((( &( "first" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((24 * retval ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (24 * retval )) ”
).

Definition solver_safety_wit_14_split_goal_1 := 
forall (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : ((n_pre - 4 ) = (-1))) (PreH2 : (retval_2 = 1)) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  ((( &( "second" ) )) # Int64  |-> retval_2)
  **  ((( &( "first" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((24 * retval ) <= INT64_MAX) ”
.

Definition solver_safety_wit_14_split_goal_2 := 
forall (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : ((n_pre - 4 ) = (-1))) (PreH2 : (retval_2 = 1)) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  ((( &( "second" ) )) # Int64  |-> retval_2)
  **  ((( &( "first" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((INT64_MIN) <= (24 * retval )) ”
.

Definition solver_safety_wit_15 := 
(
forall (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (n_pre - 4 ))) (PreH2 : (retval_2 = (Z.pow (4) ((n_pre - 4 ))))) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  ((( &( "second" ) )) # Int64  |-> retval_2)
  **  ((( &( "first" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((24 * retval ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (24 * retval )) ”
) \/
(
forall (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (n_pre - 4 ))) (PreH2 : (retval_2 = (Z.pow (4) ((n_pre - 4 ))))) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  ((( &( "second" ) )) # Int64  |-> retval_2)
  **  ((( &( "first" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((24 * retval ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (24 * retval )) ”
).

Definition solver_safety_wit_15_split_goal_1 := 
forall (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (n_pre - 4 ))) (PreH2 : (retval_2 = (Z.pow (4) ((n_pre - 4 ))))) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  ((( &( "second" ) )) # Int64  |-> retval_2)
  **  ((( &( "first" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((24 * retval ) <= INT64_MAX) ”
.

Definition solver_safety_wit_15_split_goal_2 := 
forall (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (n_pre - 4 ))) (PreH2 : (retval_2 = (Z.pow (4) ((n_pre - 4 ))))) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  ((( &( "second" ) )) # Int64  |-> retval_2)
  **  ((( &( "first" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((INT64_MIN) <= (24 * retval )) ”
.

Definition solver_safety_wit_16 := 
forall (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (n_pre - 4 ))) (PreH2 : (retval_2 = (Z.pow (4) ((n_pre - 4 ))))) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  ((( &( "second" ) )) # Int64  |-> retval_2)
  **  ((( &( "first" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (24 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 24) ”
.

Definition solver_safety_wit_17 := 
forall (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : ((n_pre - 4 ) = (-1))) (PreH2 : (retval_2 = 1)) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  ((( &( "second" ) )) # Int64  |-> retval_2)
  **  ((( &( "first" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (24 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 24) ”
.

Definition solver_safety_wit_18 := 
forall (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (n_pre - 4 ))) (PreH2 : (retval_2 = (Z.pow (4) ((n_pre - 4 ))))) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  ((( &( "second" ) )) # Int64  |-> retval_2)
  **  ((( &( "first" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition solver_safety_wit_19 := 
forall (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : ((n_pre - 4 ) = (-1))) (PreH2 : (retval_2 = 1)) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  ((( &( "second" ) )) # Int64  |-> retval_2)
  **  ((( &( "first" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition solver_safety_wit_20 := 
forall (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (n_pre - 4 ))) (PreH2 : (retval_2 = (Z.pow (4) ((n_pre - 4 ))))) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  ((( &( "second" ) )) # Int64  |-> retval_2)
  **  ((( &( "first" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (36 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 36) ”
.

Definition solver_safety_wit_21 := 
forall (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : ((n_pre - 4 ) = (-1))) (PreH2 : (retval_2 = 1)) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  ((( &( "second" ) )) # Int64  |-> retval_2)
  **  ((( &( "first" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (36 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 36) ”
.

Definition solver_return_wit_1 := 
(
forall (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (n_pre - 4 ))) (PreH2 : (retval_2 = (Z.pow (4) ((n_pre - 4 ))))) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  TT && emp 
|--
  “ (Spec n_pre ((24 * retval ) + (((n_pre - 3 ) * 36 ) * retval_2 ) ) ) ”
  &&  emp
) \/
(
forall (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (n_pre - 4 ))) (PreH2 : (retval_2 = (Z.pow (4) ((n_pre - 4 ))))) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  TT && emp 
|--
  “ (Spec n_pre ((24 * retval ) + (((n_pre - 3 ) * 36 ) * retval_2 ) ) ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (n_pre - 4 ))) (PreH2 : (retval_2 = (Z.pow (4) ((n_pre - 4 ))))) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  (Spec n_pre ((24 * retval ) + (((n_pre - 3 ) * 36 ) * retval_2 ) ) )
.

Definition solver_return_wit_2 := 
(
forall (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : ((n_pre - 4 ) = (-1))) (PreH2 : (retval_2 = 1)) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  TT && emp 
|--
  “ (Spec n_pre ((24 * retval ) + (((n_pre - 3 ) * 36 ) * retval_2 ) ) ) ”
  &&  emp
) \/
(
forall (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : ((n_pre - 4 ) = (-1))) (PreH2 : (retval_2 = 1)) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  TT && emp 
|--
  “ (Spec n_pre ((24 * retval ) + (((n_pre - 3 ) * 36 ) * 1 ) ) ) ”
  &&  emp
).

Definition solver_return_wit_2_split_goal_1 := 
forall (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : ((n_pre - 4 ) = (-1))) (PreH2 : (retval_2 = 1)) (PreH3 : (0 <= (n_pre - 3 ))) (PreH4 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 30)) ,
  (Spec n_pre ((24 * retval ) + (((n_pre - 3 ) * 36 ) * 1 ) ) )
.

Definition solver_partial_solve_wit_1_pure := 
forall (n_pre: Z) (PreH1 : (3 <= n_pre)) (PreH2 : (n_pre <= 30)) ,
  ((( &( "first" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((-1) <= (n_pre - 3 )) ” 
  &&  “ ((n_pre - 3 ) <= 27) ”
.

Definition solver_partial_solve_wit_1_aux := 
forall (n_pre: Z) (PreH1 : (3 <= n_pre)) (PreH2 : (n_pre <= 30)) ,
  TT && emp 
|--
  “ ((-1) <= (n_pre - 3 )) ” 
  &&  “ ((n_pre - 3 ) <= 27) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 30) ”
  &&  emp
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2_pure := 
forall (n_pre: Z) (retval: Z) (PreH1 : (0 <= (n_pre - 3 ))) (PreH2 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 30)) ,
  ((( &( "second" ) )) # Int64  |->_)
  **  ((( &( "first" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((-1) <= (n_pre - 4 )) ” 
  &&  “ ((n_pre - 4 ) <= 27) ”
.

Definition solver_partial_solve_wit_2_aux := 
forall (n_pre: Z) (retval: Z) (PreH1 : (0 <= (n_pre - 3 ))) (PreH2 : (retval = (Z.pow (4) ((n_pre - 3 ))))) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 30)) ,
  TT && emp 
|--
  “ ((-1) <= (n_pre - 4 )) ” 
  &&  “ ((n_pre - 4 ) <= 27) ” 
  &&  “ (0 <= (n_pre - 3 )) ” 
  &&  “ (retval = (Z.pow (4) ((n_pre - 3 )))) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 30) ”
  &&  emp
.

Definition solver_partial_solve_wit_2 := solver_partial_solve_wit_2_pure -> solver_partial_solve_wit_2_aux.

Module Type VC_Correct.


Axiom proof_of_power4_safety_wit_1 : power4_safety_wit_1.
Axiom proof_of_power4_safety_wit_2 : power4_safety_wit_2.
Axiom proof_of_power4_safety_wit_3 : power4_safety_wit_3.
Axiom proof_of_power4_safety_wit_4 : power4_safety_wit_4.
Axiom proof_of_power4_safety_wit_5 : power4_safety_wit_5.
Axiom proof_of_power4_safety_wit_6 : power4_safety_wit_6.
Axiom proof_of_power4_safety_wit_7 : power4_safety_wit_7.
Axiom proof_of_power4_safety_wit_8 : power4_safety_wit_8.
Axiom proof_of_power4_entail_wit_1 : power4_entail_wit_1.
Axiom proof_of_power4_entail_wit_2 : power4_entail_wit_2.
Axiom proof_of_power4_return_wit_1 : power4_return_wit_1.
Axiom proof_of_power4_return_wit_2 : power4_return_wit_2.
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
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.

End VC_Correct.
