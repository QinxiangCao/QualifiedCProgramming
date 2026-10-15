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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P055_567C_geometric_progression_lib.
Local Open Scope sac.

(*----- Function cmp_ll -----*)

Definition cmp_ll_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (vy: Z) (vx: Z) (PreH1 : (vx >= vy)) (PreH2 : (vx > vy)) ,
  ((( &( "b" ) )) # Int64  |-> vy)
  **  ((( &( "a" ) )) # Int64  |-> vx)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((x_pre) # Int64  |-> vx)
  **  ((y_pre) # Int64  |-> vy)
|--
  “ ((1 - 0 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (1 - 0 )) ”
.

Definition cmp_ll_safety_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (vy: Z) (vx: Z) (PreH1 : (vx < vy)) (PreH2 : (vx <= vy)) ,
  ((( &( "b" ) )) # Int64  |-> vy)
  **  ((( &( "a" ) )) # Int64  |-> vx)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((x_pre) # Int64  |-> vx)
  **  ((y_pre) # Int64  |-> vy)
|--
  “ ((0 - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (0 - 1 )) ”
.

Definition cmp_ll_safety_wit_3 := 
forall (y_pre: Z) (x_pre: Z) (vy: Z) (vx: Z) (PreH1 : (vx >= vy)) (PreH2 : (vx <= vy)) ,
  ((( &( "b" ) )) # Int64  |-> vy)
  **  ((( &( "a" ) )) # Int64  |-> vx)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((x_pre) # Int64  |-> vx)
  **  ((y_pre) # Int64  |-> vy)
|--
  “ ((0 - 0 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (0 - 0 )) ”
.

Definition cmp_ll_safety_wit_4 := 
forall (y_pre: Z) (x_pre: Z) (vy: Z) (vx: Z) (PreH1 : (vx < vy)) (PreH2 : (vx > vy)) ,
  ((( &( "b" ) )) # Int64  |-> vy)
  **  ((( &( "a" ) )) # Int64  |-> vx)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((x_pre) # Int64  |-> vx)
  **  ((y_pre) # Int64  |-> vy)
|--
  “ False ”
.

Definition cmp_ll_return_wit_1 := 
(
forall (y_pre: Z) (x_pre: Z) (vy: Z) (vx: Z) (PreH1 : (vx >= vy)) (PreH2 : (vx <= vy)) ,
  ((x_pre) # Int64  |-> vx)
  **  ((y_pre) # Int64  |-> vy)
|--
  “ (CompareResult vx vy (0 - 0 ) ) ”
  &&  ((x_pre) # Int64  |-> vx)
  **  ((y_pre) # Int64  |-> vy)
) \/
(
forall (vy: Z) (vx: Z) (PreH1 : (vx >= vy)) (PreH2 : (vx <= vy)) ,
  TT && emp 
|--
  “ (CompareResult vx vy (0 - 0 ) ) ”
  &&  emp
).

Definition cmp_ll_return_wit_1_split_goal_1 := 
forall (vy: Z) (vx: Z) (PreH1 : (vx >= vy)) (PreH2 : (vx <= vy)) ,
  (CompareResult vx vy (0 - 0 ) )
.

Definition cmp_ll_return_wit_2 := 
(
forall (y_pre: Z) (x_pre: Z) (vy: Z) (vx: Z) (PreH1 : (vx < vy)) (PreH2 : (vx <= vy)) ,
  ((x_pre) # Int64  |-> vx)
  **  ((y_pre) # Int64  |-> vy)
|--
  “ (CompareResult vx vy (0 - 1 ) ) ”
  &&  ((x_pre) # Int64  |-> vx)
  **  ((y_pre) # Int64  |-> vy)
) \/
(
forall (vy: Z) (vx: Z) (PreH1 : (vx < vy)) (PreH2 : (vx <= vy)) ,
  TT && emp 
|--
  “ (CompareResult vx vy (0 - 1 ) ) ”
  &&  emp
).

Definition cmp_ll_return_wit_2_split_goal_1 := 
forall (vy: Z) (vx: Z) (PreH1 : (vx < vy)) (PreH2 : (vx <= vy)) ,
  (CompareResult vx vy (0 - 1 ) )
.

Definition cmp_ll_return_wit_3 := 
(
forall (y_pre: Z) (x_pre: Z) (vy: Z) (vx: Z) (PreH1 : (vx >= vy)) (PreH2 : (vx > vy)) ,
  ((x_pre) # Int64  |-> vx)
  **  ((y_pre) # Int64  |-> vy)
|--
  “ (CompareResult vx vy (1 - 0 ) ) ”
  &&  ((x_pre) # Int64  |-> vx)
  **  ((y_pre) # Int64  |-> vy)
) \/
(
forall (vy: Z) (vx: Z) (PreH1 : (vx >= vy)) (PreH2 : (vx > vy)) ,
  TT && emp 
|--
  “ (CompareResult vx vy (1 - 0 ) ) ”
  &&  emp
).

Definition cmp_ll_return_wit_3_split_goal_1 := 
forall (vy: Z) (vx: Z) (PreH1 : (vx >= vy)) (PreH2 : (vx > vy)) ,
  (CompareResult vx vy (1 - 0 ) )
.

(*----- Function lower_bound_ll -----*)

Definition lower_bound_ll_safety_wit_1 := 
forall (x_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (increasing values )) ,
  ((( &( "l" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  (Int64Array.seg a_pre 0 n_pre values )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition lower_bound_ll_safety_wit_2 := 
forall (x_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (r: Z) (l: Z) (PreH1 : (l < r)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= l)) (PreH6 : (l <= r)) (PreH7 : (r <= n_pre)) (PreH8 : (increasing values )) (PreH9 : forall (i: Z) , (((0 <= i) /\ (i < l)) -> ((Znth i values 0) < x_pre))) (PreH10 : forall (i_2: Z) , (((r <= i_2) /\ (i_2 < n_pre)) -> (x_pre <= (Znth i_2 values 0)))) ,
  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (Int64Array.seg a_pre 0 n_pre values )
|--
  “ (((l + r ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition lower_bound_ll_safety_wit_3 := 
forall (x_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (r: Z) (l: Z) (PreH1 : (l < r)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= l)) (PreH6 : (l <= r)) (PreH7 : (r <= n_pre)) (PreH8 : (increasing values )) (PreH9 : forall (i: Z) , (((0 <= i) /\ (i < l)) -> ((Znth i values 0) < x_pre))) (PreH10 : forall (i_2: Z) , (((r <= i_2) /\ (i_2 < n_pre)) -> (x_pre <= (Znth i_2 values 0)))) ,
  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (Int64Array.seg a_pre 0 n_pre values )
|--
  “ ((l + r ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (l + r )) ”
.

Definition lower_bound_ll_safety_wit_4 := 
forall (x_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (r: Z) (l: Z) (PreH1 : (l < r)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= l)) (PreH6 : (l <= r)) (PreH7 : (r <= n_pre)) (PreH8 : (increasing values )) (PreH9 : forall (i: Z) , (((0 <= i) /\ (i < l)) -> ((Znth i values 0) < x_pre))) (PreH10 : forall (i_2: Z) , (((r <= i_2) /\ (i_2 < n_pre)) -> (x_pre <= (Znth i_2 values 0)))) ,
  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (Int64Array.seg a_pre 0 n_pre values )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition lower_bound_ll_safety_wit_5 := 
forall (x_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (((l + r ) ÷ 2 ) - 0 ) values 0) < x_pre)) (PreH2 : (0 <= ((l + r ) ÷ 2 ))) (PreH3 : (((l + r ) ÷ 2 ) < n_pre)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (x_pre >= INT64_MIN)) (PreH6 : (r <= INT_MAX)) (PreH7 : (l <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (r >= INT_MIN)) (PreH10 : (l >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (l < r)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : (0 <= n_pre)) (PreH15 : (n_pre <= 200000)) (PreH16 : (0 <= l)) (PreH17 : (l <= r)) (PreH18 : (r <= n_pre)) (PreH19 : (increasing values )) (PreH20 : forall (i: Z) , (((0 <= i) /\ (i < l)) -> ((Znth i values 0) < x_pre))) (PreH21 : forall (i_2: Z) , (((r <= i_2) /\ (i_2 < n_pre)) -> (x_pre <= (Znth i_2 values 0)))) ,
  (Int64Array.seg a_pre 0 n_pre values )
  **  ((( &( "m" ) )) # Int  |-> ((l + r ) ÷ 2 ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
|--
  “ ((((l + r ) ÷ 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((l + r ) ÷ 2 ) + 1 )) ”
.

Definition lower_bound_ll_safety_wit_6 := 
forall (x_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (((l + r ) ÷ 2 ) - 0 ) values 0) < x_pre)) (PreH2 : (0 <= ((l + r ) ÷ 2 ))) (PreH3 : (((l + r ) ÷ 2 ) < n_pre)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (x_pre >= INT64_MIN)) (PreH6 : (r <= INT_MAX)) (PreH7 : (l <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (r >= INT_MIN)) (PreH10 : (l >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (l < r)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : (0 <= n_pre)) (PreH15 : (n_pre <= 200000)) (PreH16 : (0 <= l)) (PreH17 : (l <= r)) (PreH18 : (r <= n_pre)) (PreH19 : (increasing values )) (PreH20 : forall (i: Z) , (((0 <= i) /\ (i < l)) -> ((Znth i values 0) < x_pre))) (PreH21 : forall (i_2: Z) , (((r <= i_2) /\ (i_2 < n_pre)) -> (x_pre <= (Znth i_2 values 0)))) ,
  (Int64Array.seg a_pre 0 n_pre values )
  **  ((( &( "m" ) )) # Int  |-> ((l + r ) ÷ 2 ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition lower_bound_ll_entail_wit_1 := 
(
forall (x_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (increasing values )) ,
  (Int64Array.seg a_pre 0 n_pre values )
|--
  “ (n_pre = (Zlength (values))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= n_pre) ” 
  &&  “ (increasing values ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < 0)) -> ((Znth i values 0) < x_pre)) ” 
  &&  “ forall (i_2: Z) , (((n_pre <= i_2) /\ (i_2 < n_pre)) -> (x_pre <= (Znth i_2 values 0))) ”
  &&  (Int64Array.seg a_pre 0 n_pre values )
) \/
(
forall (x_pre: Z) (n_pre: Z) (values: (@list Z)) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (increasing values )) ,
  TT && emp 
|--
  “ forall (i_2: Z) , (((n_pre <= i_2) /\ (i_2 < n_pre)) -> (x_pre <= (Znth i_2 values 0))) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < 0)) -> ((Znth i values 0) < x_pre)) ”
  &&  emp
).

Definition lower_bound_ll_entail_wit_1_split_goal_1 := 
forall (x_pre: Z) (n_pre: Z) (values: (@list Z)) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (increasing values )) ,
  forall (i_2: Z) , (((n_pre <= i_2) /\ (i_2 < n_pre)) -> (x_pre <= (Znth i_2 values 0)))
.

Definition lower_bound_ll_entail_wit_1_split_goal_2 := 
forall (x_pre: Z) (n_pre: Z) (values: (@list Z)) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (increasing values )) ,
  forall (i: Z) , (((0 <= i) /\ (i < 0)) -> ((Znth i values 0) < x_pre))
.

Definition lower_bound_ll_entail_wit_2 := 
(
forall (x_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (r: Z) (l: Z) (PreH1 : (l < r)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= l)) (PreH6 : (l <= r)) (PreH7 : (r <= n_pre)) (PreH8 : (increasing values )) (PreH9 : forall (i: Z) , (((0 <= i) /\ (i < l)) -> ((Znth i values 0) < x_pre))) (PreH10 : forall (i_2: Z) , (((r <= i_2) /\ (i_2 < n_pre)) -> (x_pre <= (Znth i_2 values 0)))) ,
  ((( &( "m" ) )) # Int  |-> ((l + r ) ÷ 2 ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (Int64Array.seg a_pre 0 n_pre values )
|--
  “ (0 <= ((l + r ) ÷ 2 )) ” 
  &&  “ (((l + r ) ÷ 2 ) < n_pre) ” 
  &&  “ (x_pre <= INT64_MAX) ” 
  &&  “ (x_pre >= INT64_MIN) ” 
  &&  “ (r <= INT_MAX) ” 
  &&  “ (l <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (r >= INT_MIN) ” 
  &&  “ (l >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (l < r) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (0 <= l) ” 
  &&  “ (l <= r) ” 
  &&  “ (r <= n_pre) ” 
  &&  “ (increasing values ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < l)) -> ((Znth i values 0) < x_pre)) ” 
  &&  “ forall (i_2: Z) , (((r <= i_2) /\ (i_2 < n_pre)) -> (x_pre <= (Znth i_2 values 0))) ”
  &&  ((( &( "m" ) )) # Int  |-> ((l + r ) ÷ 2 ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (Int64Array.seg a_pre 0 n_pre values )
) \/
(
forall (x_pre: Z) (n_pre: Z) (values: (@list Z)) (r: Z) (l: Z) (PreH1 : (x_pre <= INT64_MAX)) (PreH2 : (x_pre >= INT64_MIN)) (PreH3 : (r <= INT_MAX)) (PreH4 : (l <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (((l + r ) ÷ 2 ) <= INT_MAX)) (PreH7 : (r >= INT_MIN)) (PreH8 : (l >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : (((l + r ) ÷ 2 ) >= INT_MIN)) (PreH11 : (l < r)) (PreH12 : (n_pre = (Zlength (values)))) (PreH13 : (0 <= n_pre)) (PreH14 : (n_pre <= 200000)) (PreH15 : (0 <= l)) (PreH16 : (l <= r)) (PreH17 : (r <= n_pre)) (PreH18 : (increasing values )) (PreH19 : forall (i: Z) , (((0 <= i) /\ (i < l)) -> ((Znth i values 0) < x_pre))) (PreH20 : forall (i_2: Z) , (((r <= i_2) /\ (i_2 < n_pre)) -> (x_pre <= (Znth i_2 values 0)))) ,
  TT && emp 
|--
  “ (((l + r ) ÷ 2 ) < n_pre) ” 
  &&  “ (0 <= ((l + r ) ÷ 2 )) ”
  &&  emp
).

Definition lower_bound_ll_entail_wit_2_split_goal_1 := 
forall (x_pre: Z) (n_pre: Z) (values: (@list Z)) (r: Z) (l: Z) (PreH1 : (x_pre <= INT64_MAX)) (PreH2 : (x_pre >= INT64_MIN)) (PreH3 : (r <= INT_MAX)) (PreH4 : (l <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (((l + r ) ÷ 2 ) <= INT_MAX)) (PreH7 : (r >= INT_MIN)) (PreH8 : (l >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : (((l + r ) ÷ 2 ) >= INT_MIN)) (PreH11 : (l < r)) (PreH12 : (n_pre = (Zlength (values)))) (PreH13 : (0 <= n_pre)) (PreH14 : (n_pre <= 200000)) (PreH15 : (0 <= l)) (PreH16 : (l <= r)) (PreH17 : (r <= n_pre)) (PreH18 : (increasing values )) (PreH19 : forall (i: Z) , (((0 <= i) /\ (i < l)) -> ((Znth i values 0) < x_pre))) (PreH20 : forall (i_2: Z) , (((r <= i_2) /\ (i_2 < n_pre)) -> (x_pre <= (Znth i_2 values 0)))) ,
  (((l + r ) ÷ 2 ) < n_pre)
.

Definition lower_bound_ll_entail_wit_2_split_goal_2 := 
forall (x_pre: Z) (n_pre: Z) (values: (@list Z)) (r: Z) (l: Z) (PreH1 : (x_pre <= INT64_MAX)) (PreH2 : (x_pre >= INT64_MIN)) (PreH3 : (r <= INT_MAX)) (PreH4 : (l <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (((l + r ) ÷ 2 ) <= INT_MAX)) (PreH7 : (r >= INT_MIN)) (PreH8 : (l >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : (((l + r ) ÷ 2 ) >= INT_MIN)) (PreH11 : (l < r)) (PreH12 : (n_pre = (Zlength (values)))) (PreH13 : (0 <= n_pre)) (PreH14 : (n_pre <= 200000)) (PreH15 : (0 <= l)) (PreH16 : (l <= r)) (PreH17 : (r <= n_pre)) (PreH18 : (increasing values )) (PreH19 : forall (i: Z) , (((0 <= i) /\ (i < l)) -> ((Znth i values 0) < x_pre))) (PreH20 : forall (i_2: Z) , (((r <= i_2) /\ (i_2 < n_pre)) -> (x_pre <= (Znth i_2 values 0)))) ,
  (0 <= ((l + r ) ÷ 2 ))
.

Definition lower_bound_ll_entail_wit_3_1 := 
(
forall (x_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (((l + r ) ÷ 2 ) - 0 ) values 0) < x_pre)) (PreH2 : (0 <= ((l + r ) ÷ 2 ))) (PreH3 : (((l + r ) ÷ 2 ) < n_pre)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (x_pre >= INT64_MIN)) (PreH6 : (r <= INT_MAX)) (PreH7 : (l <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (r >= INT_MIN)) (PreH10 : (l >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (l < r)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : (0 <= n_pre)) (PreH15 : (n_pre <= 200000)) (PreH16 : (0 <= l)) (PreH17 : (l <= r)) (PreH18 : (r <= n_pre)) (PreH19 : (increasing values )) (PreH20 : forall (i: Z) , (((0 <= i) /\ (i < l)) -> ((Znth i values 0) < x_pre))) (PreH21 : forall (i_2: Z) , (((r <= i_2) /\ (i_2 < n_pre)) -> (x_pre <= (Znth i_2 values 0)))) ,
  (Int64Array.seg a_pre 0 n_pre values )
|--
  “ (n_pre = (Zlength (values))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (0 <= (((l + r ) ÷ 2 ) + 1 )) ” 
  &&  “ ((((l + r ) ÷ 2 ) + 1 ) <= r) ” 
  &&  “ (r <= n_pre) ” 
  &&  “ (increasing values ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (((l + r ) ÷ 2 ) + 1 ))) -> ((Znth i values 0) < x_pre)) ” 
  &&  “ forall (i_2: Z) , (((r <= i_2) /\ (i_2 < n_pre)) -> (x_pre <= (Znth i_2 values 0))) ”
  &&  (Int64Array.seg a_pre 0 n_pre values )
) \/
(
forall (x_pre: Z) (n_pre: Z) (values: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (((l + r ) ÷ 2 ) - 0 ) values 0) < x_pre)) (PreH2 : (0 <= ((l + r ) ÷ 2 ))) (PreH3 : (((l + r ) ÷ 2 ) < n_pre)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (x_pre >= INT64_MIN)) (PreH6 : (r <= INT_MAX)) (PreH7 : (l <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (r >= INT_MIN)) (PreH10 : (l >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (l < r)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : (0 <= n_pre)) (PreH15 : (n_pre <= 200000)) (PreH16 : (0 <= l)) (PreH17 : (l <= r)) (PreH18 : (r <= n_pre)) (PreH19 : (increasing values )) (PreH20 : forall (i: Z) , (((0 <= i) /\ (i < l)) -> ((Znth i values 0) < x_pre))) (PreH21 : forall (i_2: Z) , (((r <= i_2) /\ (i_2 < n_pre)) -> (x_pre <= (Znth i_2 values 0)))) ,
  TT && emp 
|--
  “ ((((l + r ) ÷ 2 ) + 1 ) <= r) ”
  &&  emp
).

Definition lower_bound_ll_entail_wit_3_1_split_goal_1 := 
forall (x_pre: Z) (n_pre: Z) (values: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (((l + r ) ÷ 2 ) - 0 ) values 0) < x_pre)) (PreH2 : (0 <= ((l + r ) ÷ 2 ))) (PreH3 : (((l + r ) ÷ 2 ) < n_pre)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (x_pre >= INT64_MIN)) (PreH6 : (r <= INT_MAX)) (PreH7 : (l <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (r >= INT_MIN)) (PreH10 : (l >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (l < r)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : (0 <= n_pre)) (PreH15 : (n_pre <= 200000)) (PreH16 : (0 <= l)) (PreH17 : (l <= r)) (PreH18 : (r <= n_pre)) (PreH19 : (increasing values )) (PreH20 : forall (i: Z) , (((0 <= i) /\ (i < l)) -> ((Znth i values 0) < x_pre))) (PreH21 : forall (i_2: Z) , (((r <= i_2) /\ (i_2 < n_pre)) -> (x_pre <= (Znth i_2 values 0)))) ,
  ((((l + r ) ÷ 2 ) + 1 ) <= r)
.

Definition lower_bound_ll_entail_wit_3_2 := 
(
forall (x_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (((l + r ) ÷ 2 ) - 0 ) values 0) >= x_pre)) (PreH2 : (0 <= ((l + r ) ÷ 2 ))) (PreH3 : (((l + r ) ÷ 2 ) < n_pre)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (x_pre >= INT64_MIN)) (PreH6 : (r <= INT_MAX)) (PreH7 : (l <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (r >= INT_MIN)) (PreH10 : (l >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (l < r)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : (0 <= n_pre)) (PreH15 : (n_pre <= 200000)) (PreH16 : (0 <= l)) (PreH17 : (l <= r)) (PreH18 : (r <= n_pre)) (PreH19 : (increasing values )) (PreH20 : forall (i: Z) , (((0 <= i) /\ (i < l)) -> ((Znth i values 0) < x_pre))) (PreH21 : forall (i_2: Z) , (((r <= i_2) /\ (i_2 < n_pre)) -> (x_pre <= (Znth i_2 values 0)))) ,
  (Int64Array.seg a_pre 0 n_pre values )
|--
  “ (n_pre = (Zlength (values))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (0 <= l) ” 
  &&  “ (l <= ((l + r ) ÷ 2 )) ” 
  &&  “ (((l + r ) ÷ 2 ) <= n_pre) ” 
  &&  “ (increasing values ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < l)) -> ((Znth i values 0) < x_pre)) ” 
  &&  “ forall (i_2: Z) , (((((l + r ) ÷ 2 ) <= i_2) /\ (i_2 < n_pre)) -> (x_pre <= (Znth i_2 values 0))) ”
  &&  (Int64Array.seg a_pre 0 n_pre values )
) \/
(
forall (x_pre: Z) (n_pre: Z) (values: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (((l + r ) ÷ 2 ) - 0 ) values 0) >= x_pre)) (PreH2 : (0 <= ((l + r ) ÷ 2 ))) (PreH3 : (((l + r ) ÷ 2 ) < n_pre)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (x_pre >= INT64_MIN)) (PreH6 : (r <= INT_MAX)) (PreH7 : (l <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (r >= INT_MIN)) (PreH10 : (l >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (l < r)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : (0 <= n_pre)) (PreH15 : (n_pre <= 200000)) (PreH16 : (0 <= l)) (PreH17 : (l <= r)) (PreH18 : (r <= n_pre)) (PreH19 : (increasing values )) (PreH20 : forall (i: Z) , (((0 <= i) /\ (i < l)) -> ((Znth i values 0) < x_pre))) (PreH21 : forall (i_2: Z) , (((r <= i_2) /\ (i_2 < n_pre)) -> (x_pre <= (Znth i_2 values 0)))) ,
  TT && emp 
|--
  “ (l <= ((l + r ) ÷ 2 )) ”
  &&  emp
).

Definition lower_bound_ll_entail_wit_3_2_split_goal_1 := 
forall (x_pre: Z) (n_pre: Z) (values: (@list Z)) (r: Z) (l: Z) (PreH1 : ((Znth (((l + r ) ÷ 2 ) - 0 ) values 0) >= x_pre)) (PreH2 : (0 <= ((l + r ) ÷ 2 ))) (PreH3 : (((l + r ) ÷ 2 ) < n_pre)) (PreH4 : (x_pre <= INT64_MAX)) (PreH5 : (x_pre >= INT64_MIN)) (PreH6 : (r <= INT_MAX)) (PreH7 : (l <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (r >= INT_MIN)) (PreH10 : (l >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (l < r)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : (0 <= n_pre)) (PreH15 : (n_pre <= 200000)) (PreH16 : (0 <= l)) (PreH17 : (l <= r)) (PreH18 : (r <= n_pre)) (PreH19 : (increasing values )) (PreH20 : forall (i: Z) , (((0 <= i) /\ (i < l)) -> ((Znth i values 0) < x_pre))) (PreH21 : forall (i_2: Z) , (((r <= i_2) /\ (i_2 < n_pre)) -> (x_pre <= (Znth i_2 values 0)))) ,
  (l <= ((l + r ) ÷ 2 ))
.

Definition lower_bound_ll_return_wit_1 := 
(
forall (x_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (r: Z) (l: Z) (PreH1 : (l >= r)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= l)) (PreH6 : (l <= r)) (PreH7 : (r <= n_pre)) (PreH8 : (increasing values )) (PreH9 : forall (i: Z) , (((0 <= i) /\ (i < l)) -> ((Znth i values 0) < x_pre))) (PreH10 : forall (i_2: Z) , (((r <= i_2) /\ (i_2 < n_pre)) -> (x_pre <= (Znth i_2 values 0)))) ,
  (Int64Array.seg a_pre 0 n_pre values )
|--
  “ (0 <= l) ” 
  &&  “ (l <= n_pre) ” 
  &&  “ (LowerBoundResult values x_pre l ) ”
  &&  (Int64Array.seg a_pre 0 n_pre values )
) \/
(
forall (x_pre: Z) (n_pre: Z) (values: (@list Z)) (r: Z) (l: Z) (PreH1 : (l >= r)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= l)) (PreH6 : (l <= r)) (PreH7 : (r <= n_pre)) (PreH8 : (increasing values )) (PreH9 : forall (i: Z) , (((0 <= i) /\ (i < l)) -> ((Znth i values 0) < x_pre))) (PreH10 : forall (i_2: Z) , (((r <= i_2) /\ (i_2 < n_pre)) -> (x_pre <= (Znth i_2 values 0)))) ,
  TT && emp 
|--
  “ (LowerBoundResult values x_pre l ) ”
  &&  emp
).

Definition lower_bound_ll_return_wit_1_split_goal_1 := 
forall (x_pre: Z) (n_pre: Z) (values: (@list Z)) (r: Z) (l: Z) (PreH1 : (l >= r)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (0 <= l)) (PreH6 : (l <= r)) (PreH7 : (r <= n_pre)) (PreH8 : (increasing values )) (PreH9 : forall (i: Z) , (((0 <= i) /\ (i < l)) -> ((Znth i values 0) < x_pre))) (PreH10 : forall (i_2: Z) , (((r <= i_2) /\ (i_2 < n_pre)) -> (x_pre <= (Znth i_2 values 0)))) ,
  (LowerBoundResult values x_pre l )
.

Definition lower_bound_ll_partial_solve_wit_1 := 
forall (x_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (r: Z) (l: Z) (PreH1 : (0 <= ((l + r ) ÷ 2 ))) (PreH2 : (((l + r ) ÷ 2 ) < n_pre)) (PreH3 : (x_pre <= INT64_MAX)) (PreH4 : (x_pre >= INT64_MIN)) (PreH5 : (r <= INT_MAX)) (PreH6 : (l <= INT_MAX)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (r >= INT_MIN)) (PreH9 : (l >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (l < r)) (PreH12 : (n_pre = (Zlength (values)))) (PreH13 : (0 <= n_pre)) (PreH14 : (n_pre <= 200000)) (PreH15 : (0 <= l)) (PreH16 : (l <= r)) (PreH17 : (r <= n_pre)) (PreH18 : (increasing values )) (PreH19 : forall (i: Z) , (((0 <= i) /\ (i < l)) -> ((Znth i values 0) < x_pre))) (PreH20 : forall (i_2: Z) , (((r <= i_2) /\ (i_2 < n_pre)) -> (x_pre <= (Znth i_2 values 0)))) ,
  (Int64Array.seg a_pre 0 n_pre values )
|--
  “ (0 <= ((l + r ) ÷ 2 )) ” 
  &&  “ (((l + r ) ÷ 2 ) < n_pre) ” 
  &&  “ (x_pre <= INT64_MAX) ” 
  &&  “ (x_pre >= INT64_MIN) ” 
  &&  “ (r <= INT_MAX) ” 
  &&  “ (l <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (r >= INT_MIN) ” 
  &&  “ (l >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (l < r) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (0 <= l) ” 
  &&  “ (l <= r) ” 
  &&  “ (r <= n_pre) ” 
  &&  “ (increasing values ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < l)) -> ((Znth i values 0) < x_pre)) ” 
  &&  “ forall (i_2: Z) , (((r <= i_2) /\ (i_2 < n_pre)) -> (x_pre <= (Znth i_2 values 0))) ”
  &&  (((a_pre + (((l + r ) ÷ 2 ) * sizeof(INT64)))) # Int64  |-> (Znth (((l + r ) ÷ 2 ) - 0 ) values 0))
  **  (Int64Array.missing_i a_pre ((l + r ) ÷ 2 ) 0 n_pre values )
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 200000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> (((-1000000000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (values)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (Int64Array.undef_full retval_2 n_pre )
  **  ((( &( "vals" ) )) # Ptr  |-> retval_2)
  **  (Int64Array.undef_full retval n_pre )
  **  ((( &( "a" ) )) # Ptr  |-> retval)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  (Int64Array.full input_pre n_pre values )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (i: Z) (vals: Z) (a: Z) (PreH1 : (i < n_pre)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 200000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) ,
  (Int64Array.seg vals 0 (i + 1 ) (app ((sublist (0) (i) (values))) ((cons ((Znth i values 0)) ((@nil Z))))) )
  **  (Int64Array.undef_seg vals (i + 1 ) n_pre )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg a 0 (i + 1 ) (app ((sublist (0) (i) (values))) ((cons ((Znth i values 0)) ((@nil Z))))) )
  **  (Int64Array.undef_seg a (i + 1 ) n_pre )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_3 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (a: Z) (vals: Z) (sorted: (@list Z)) (PreH1 : (Permutation values sorted )) (PreH2 : (increasing sorted )) (PreH3 : ((Zlength (sorted)) = n_pre)) (PreH4 : (a <> 0)) (PreH5 : (vals <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) ,
  ((( &( "un" ) )) # Int  |->_)
  **  (Int64Array.full vals n_pre sorted )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (a: Z) (vals: Z) (sorted: (@list Z)) (PreH1 : (Permutation values sorted )) (PreH2 : (increasing sorted )) (PreH3 : ((Zlength (sorted)) = n_pre)) (PreH4 : (a <> 0)) (PreH5 : (vals <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "un" ) )) # Int  |-> 0)
  **  (Int64Array.full vals n_pre sorted )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_5 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (un: Z) (i: Z) (storage: (@list Z)) (sorted: (@list Z)) (vals: Z) (a: Z) (PreH1 : (i < n_pre)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 200000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : ((Zlength (sorted)) = n_pre)) (PreH11 : ((Zlength (storage)) = n_pre)) (PreH12 : (Permutation values sorted )) (PreH13 : (increasing sorted )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= un)) (PreH17 : (un <= i)) (PreH18 : (CompressionState sorted i un storage )) ,
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full vals n_pre storage )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_6 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (un: Z) (i: Z) (storage: (@list Z)) (sorted: (@list Z)) (vals: Z) (a: Z) (PreH1 : (i <> 0)) (PreH2 : (i < n_pre)) (PreH3 : (a <> 0)) (PreH4 : (vals <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 200000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : ((Zlength (storage)) = n_pre)) (PreH13 : (Permutation values sorted )) (PreH14 : (increasing sorted )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= un)) (PreH18 : (un <= i)) (PreH19 : (CompressionState sorted i un storage )) ,
  (Int64Array.full vals n_pre storage )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_7 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (un: Z) (i: Z) (storage: (@list Z)) (sorted: (@list Z)) (vals: Z) (a: Z) (PreH1 : (i <> 0)) (PreH2 : (i < n_pre)) (PreH3 : (a <> 0)) (PreH4 : (vals <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 200000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : ((Zlength (storage)) = n_pre)) (PreH13 : (Permutation values sorted )) (PreH14 : (increasing sorted )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= un)) (PreH18 : (un <= i)) (PreH19 : (CompressionState sorted i un storage )) ,
  (Int64Array.full vals n_pre storage )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_8 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (un: Z) (i: Z) (storage: (@list Z)) (sorted: (@list Z)) (vals: Z) (a: Z) (PreH1 : (i = 0)) (PreH2 : (i < n_pre)) (PreH3 : (a <> 0)) (PreH4 : (vals <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 200000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : ((Zlength (storage)) = n_pre)) (PreH13 : (Permutation values sorted )) (PreH14 : (increasing sorted )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= un)) (PreH18 : (un <= i)) (PreH19 : (CompressionState sorted i un storage )) ,
  (Int64Array.full vals n_pre (replace_Znth (un) ((Znth i storage 0)) (storage)) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
|--
  “ ((un + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (un + 1 )) ”
.

Definition solver_safety_wit_9 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (un: Z) (i: Z) (storage: (@list Z)) (sorted: (@list Z)) (vals: Z) (a: Z) (PreH1 : ((Znth i storage 0) <> (Znth (i - 1 ) storage 0))) (PreH2 : (i <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (a <> 0)) (PreH5 : (vals <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : ((Zlength (storage)) = n_pre)) (PreH14 : (Permutation values sorted )) (PreH15 : (increasing sorted )) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= un)) (PreH19 : (un <= i)) (PreH20 : (CompressionState sorted i un storage )) ,
  (Int64Array.full vals n_pre (replace_Znth (un) ((Znth i storage 0)) (storage)) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
|--
  “ ((un + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (un + 1 )) ”
.

Definition solver_safety_wit_10 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (un: Z) (i: Z) (storage: (@list Z)) (sorted: (@list Z)) (vals: Z) (a: Z) (PreH1 : (i = 0)) (PreH2 : (i < n_pre)) (PreH3 : (a <> 0)) (PreH4 : (vals <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 200000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : ((Zlength (storage)) = n_pre)) (PreH13 : (Permutation values sorted )) (PreH14 : (increasing sorted )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= un)) (PreH18 : (un <= i)) (PreH19 : (CompressionState sorted i un storage )) ,
  (Int64Array.full vals n_pre (replace_Znth (un) ((Znth i storage 0)) (storage)) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "un" ) )) # Int  |-> (un + 1 ))
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_11 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (un: Z) (i: Z) (storage: (@list Z)) (sorted: (@list Z)) (vals: Z) (a: Z) (PreH1 : ((Znth i storage 0) <> (Znth (i - 1 ) storage 0))) (PreH2 : (i <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (a <> 0)) (PreH5 : (vals <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : ((Zlength (storage)) = n_pre)) (PreH14 : (Permutation values sorted )) (PreH15 : (increasing sorted )) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= un)) (PreH19 : (un <= i)) (PreH20 : (CompressionState sorted i un storage )) ,
  (Int64Array.full vals n_pre (replace_Znth (un) ((Znth i storage 0)) (storage)) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "un" ) )) # Int  |-> (un + 1 ))
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_12 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (un: Z) (i: Z) (storage: (@list Z)) (sorted: (@list Z)) (vals: Z) (a: Z) (PreH1 : ((Znth i storage 0) = (Znth (i - 1 ) storage 0))) (PreH2 : (i <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (a <> 0)) (PreH5 : (vals <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : ((Zlength (storage)) = n_pre)) (PreH14 : (Permutation values sorted )) (PreH15 : (increasing sorted )) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= un)) (PreH19 : (un <= i)) (PreH20 : (CompressionState sorted i un storage )) ,
  (Int64Array.full vals n_pre storage )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_13 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (a: Z) (vals: Z) (un: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (a <> 0)) (PreH4 : (vals <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 200000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : (1 <= un)) (PreH11 : (un <= n_pre)) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : ((Zlength (keys)) = un)) (PreH14 : ((Zlength (tail)) = (n_pre - un ))) (PreH15 : (Permutation values sorted )) (PreH16 : (increasing sorted )) (PreH17 : (UniqueKeys sorted keys )) (PreH18 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH19 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (Int64Array.full retval_2 un (repeat_Z (0) (un)) )
  **  ((( &( "right" ) )) # Ptr  |-> retval_2)
  **  (Int64Array.full retval un (repeat_Z (0) (un)) )
  **  ((( &( "left" ) )) # Ptr  |-> retval)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_14 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (index: Z) (PreH1 : (a <> 0)) (PreH2 : (vals <> 0)) (PreH3 : (left <> 0)) (PreH4 : (right <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 200000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : (1 <= un)) (PreH11 : (un <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((Zlength (sorted)) = n_pre)) (PreH15 : ((Zlength (keys)) = un)) (PreH16 : ((Zlength (tail)) = (n_pre - un ))) (PreH17 : ((Zlength (left_data)) = un)) (PreH18 : ((Zlength (right_data)) = un)) (PreH19 : (Permutation values sorted )) (PreH20 : (increasing sorted )) (PreH21 : (UniqueKeys sorted keys )) (PreH22 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH23 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH24 : (0 <= index)) (PreH25 : (index < un)) (PreH26 : (KeyAt keys (Znth i values 0) index )) (PreH27 : (RightBuildState values i keys right_data )) (PreH28 : (left_data = (repeat_Z (0) (un)))) (PreH29 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 right_data 0)) /\ ((Znth j_3 right_data 0) <= i)))) ,
  (Int64Array.full right un right_data )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
|--
  “ (((Znth index right_data 0) + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth index right_data 0) + 1 )) ”
.

Definition solver_safety_wit_15 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (index: Z) (PreH1 : (a <> 0)) (PreH2 : (vals <> 0)) (PreH3 : (left <> 0)) (PreH4 : (right <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 200000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : (1 <= un)) (PreH11 : (un <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((Zlength (sorted)) = n_pre)) (PreH15 : ((Zlength (keys)) = un)) (PreH16 : ((Zlength (tail)) = (n_pre - un ))) (PreH17 : ((Zlength (left_data)) = un)) (PreH18 : ((Zlength (right_data)) = un)) (PreH19 : (Permutation values sorted )) (PreH20 : (increasing sorted )) (PreH21 : (UniqueKeys sorted keys )) (PreH22 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH23 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH24 : (0 <= index)) (PreH25 : (index < un)) (PreH26 : (KeyAt keys (Znth i values 0) index )) (PreH27 : (RightBuildState values i keys right_data )) (PreH28 : (left_data = (repeat_Z (0) (un)))) (PreH29 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 right_data 0)) /\ ((Znth j_3 right_data 0) <= i)))) ,
  (Int64Array.full right un (replace_Znth (index) (((Znth index right_data 0) + 1 )) (right_data)) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_16 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (i: Z) (right_data: (@list Z)) (left_data: (@list Z)) (tail: (@list Z)) (keys: (@list Z)) (sorted: (@list Z)) (un: Z) (right: Z) (left: Z) (vals: Z) (a: Z) (PreH1 : (i >= n_pre)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (left <> 0)) (PreH5 : (right <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (1 <= un)) (PreH12 : (un <= n_pre)) (PreH13 : ((Zlength (sorted)) = n_pre)) (PreH14 : ((Zlength (keys)) = un)) (PreH15 : ((Zlength (tail)) = (n_pre - un ))) (PreH16 : ((Zlength (left_data)) = un)) (PreH17 : ((Zlength (right_data)) = un)) (PreH18 : (Permutation values sorted )) (PreH19 : (increasing sorted )) (PreH20 : (UniqueKeys sorted keys )) (PreH21 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH22 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH23 : (0 <= i)) (PreH24 : (i <= n_pre)) (PreH25 : (RightBuildState values i keys right_data )) (PreH26 : (left_data = (repeat_Z (0) (un)))) (PreH27 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 right_data 0)) /\ ((Znth j_3 right_data 0) <= i)))) ,
  ((( &( "ans" ) )) # Int64  |->_)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.full right un right_data )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_17 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (i: Z) (right_data: (@list Z)) (left_data: (@list Z)) (tail: (@list Z)) (keys: (@list Z)) (sorted: (@list Z)) (un: Z) (right: Z) (left: Z) (vals: Z) (a: Z) (PreH1 : (i >= n_pre)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (left <> 0)) (PreH5 : (right <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (1 <= un)) (PreH12 : (un <= n_pre)) (PreH13 : ((Zlength (sorted)) = n_pre)) (PreH14 : ((Zlength (keys)) = un)) (PreH15 : ((Zlength (tail)) = (n_pre - un ))) (PreH16 : ((Zlength (left_data)) = un)) (PreH17 : ((Zlength (right_data)) = un)) (PreH18 : (Permutation values sorted )) (PreH19 : (increasing sorted )) (PreH20 : (UniqueKeys sorted keys )) (PreH21 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH22 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH23 : (0 <= i)) (PreH24 : (i <= n_pre)) (PreH25 : (RightBuildState values i keys right_data )) (PreH26 : (left_data = (repeat_Z (0) (un)))) (PreH27 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 right_data 0)) /\ ((Znth j_3 right_data 0) <= i)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int64  |-> 0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.full right un right_data )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_18 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (PreH1 : (a <> 0)) (PreH2 : (vals <> 0)) (PreH3 : (left <> 0)) (PreH4 : (right <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 200000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : (1 <= un)) (PreH11 : (un <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH16 : ((Zlength (sorted)) = n_pre)) (PreH17 : ((Zlength (keys)) = un)) (PreH18 : ((Zlength (tail)) = (n_pre - un ))) (PreH19 : ((Zlength (left_data)) = un)) (PreH20 : ((Zlength (right_data)) = un)) (PreH21 : (Permutation values sorted )) (PreH22 : (increasing sorted )) (PreH23 : (UniqueKeys sorted keys )) (PreH24 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH25 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH26 : (0 <= ix)) (PreH27 : (ix < un)) (PreH28 : (KeyAt keys (Znth i values 0) ix )) (PreH29 : (CountingState k_pre values i keys left_data right_data ans )) (PreH30 : (1 <= (Znth ix right_data 0))) (PreH31 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH32 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH33 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full right un right_data )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  ((( &( "ix" ) )) # Int  |-> ix)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
|--
  “ (((Znth ix right_data 0) - 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ix right_data 0) - 1 )) ”
.

Definition solver_safety_wit_19 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (PreH1 : (a <> 0)) (PreH2 : (vals <> 0)) (PreH3 : (left <> 0)) (PreH4 : (right <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 200000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : (1 <= un)) (PreH11 : (un <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH16 : ((Zlength (sorted)) = n_pre)) (PreH17 : ((Zlength (keys)) = un)) (PreH18 : ((Zlength (tail)) = (n_pre - un ))) (PreH19 : ((Zlength (left_data)) = un)) (PreH20 : ((Zlength (right_data)) = un)) (PreH21 : (Permutation values sorted )) (PreH22 : (increasing sorted )) (PreH23 : (UniqueKeys sorted keys )) (PreH24 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH25 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH26 : (0 <= ix)) (PreH27 : (ix < un)) (PreH28 : (KeyAt keys (Znth i values 0) ix )) (PreH29 : (CountingState k_pre values i keys left_data right_data ans )) (PreH30 : (1 <= (Znth ix right_data 0))) (PreH31 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH32 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH33 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  ((( &( "ix" ) )) # Int  |-> ix)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
|--
  “ (((Znth i values 0) <> (INT64_MIN)) \/ (k_pre <> (-1))) ” 
  &&  “ (k_pre <> 0) ”
.

Definition solver_safety_wit_20 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (PreH1 : (a <> 0)) (PreH2 : (vals <> 0)) (PreH3 : (left <> 0)) (PreH4 : (right <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 200000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : (1 <= un)) (PreH11 : (un <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH16 : ((Zlength (sorted)) = n_pre)) (PreH17 : ((Zlength (keys)) = un)) (PreH18 : ((Zlength (tail)) = (n_pre - un ))) (PreH19 : ((Zlength (left_data)) = un)) (PreH20 : ((Zlength (right_data)) = un)) (PreH21 : (Permutation values sorted )) (PreH22 : (increasing sorted )) (PreH23 : (UniqueKeys sorted keys )) (PreH24 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH25 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH26 : (0 <= ix)) (PreH27 : (ix < un)) (PreH28 : (KeyAt keys (Znth i values 0) ix )) (PreH29 : (CountingState k_pre values i keys left_data right_data ans )) (PreH30 : (1 <= (Znth ix right_data 0))) (PreH31 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH32 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH33 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  ((( &( "ix" ) )) # Int  |-> ix)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_21 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (PreH1 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (left <> 0)) (PreH5 : (right <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (1 <= un)) (PreH12 : (un <= n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= ans)) (PreH16 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH17 : ((Zlength (sorted)) = n_pre)) (PreH18 : ((Zlength (keys)) = un)) (PreH19 : ((Zlength (tail)) = (n_pre - un ))) (PreH20 : ((Zlength (left_data)) = un)) (PreH21 : ((Zlength (right_data)) = un)) (PreH22 : (Permutation values sorted )) (PreH23 : (increasing sorted )) (PreH24 : (UniqueKeys sorted keys )) (PreH25 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH26 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH27 : (0 <= ix)) (PreH28 : (ix < un)) (PreH29 : (KeyAt keys (Znth i values 0) ix )) (PreH30 : (CountingState k_pre values i keys left_data right_data ans )) (PreH31 : (1 <= (Znth ix right_data 0))) (PreH32 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH33 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH34 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full a n_pre values )
  **  ((( &( "lo" ) )) # Int64  |->_)
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  ((( &( "ix" ) )) # Int  |-> ix)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
|--
  “ (((Znth i values 0) <> (INT64_MIN)) \/ (k_pre <> (-1))) ” 
  &&  “ (k_pre <> 0) ”
.

Definition solver_safety_wit_22 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (PreH1 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (left <> 0)) (PreH5 : (right <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (1 <= un)) (PreH12 : (un <= n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= ans)) (PreH16 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH17 : ((Zlength (sorted)) = n_pre)) (PreH18 : ((Zlength (keys)) = un)) (PreH19 : ((Zlength (tail)) = (n_pre - un ))) (PreH20 : ((Zlength (left_data)) = un)) (PreH21 : ((Zlength (right_data)) = un)) (PreH22 : (Permutation values sorted )) (PreH23 : (increasing sorted )) (PreH24 : (UniqueKeys sorted keys )) (PreH25 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH26 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH27 : (0 <= ix)) (PreH28 : (ix < un)) (PreH29 : (KeyAt keys (Znth i values 0) ix )) (PreH30 : (CountingState k_pre values i keys left_data right_data ans )) (PreH31 : (1 <= (Znth ix right_data 0))) (PreH32 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH33 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH34 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full a n_pre values )
  **  ((( &( "hi" ) )) # Int64  |->_)
  **  ((( &( "lo" ) )) # Int64  |-> ((Znth i values 0) ÷ k_pre ))
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  ((( &( "ix" ) )) # Int  |-> ix)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
|--
  “ (((Znth i values 0) * k_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth i values 0) * k_pre )) ”
.

Definition solver_safety_wit_23 := 
(
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth (retval_2 - 0 ) keys 0) = ((Znth i values 0) * k_pre ))) (PreH2 : (retval_2 < un)) (PreH3 : ((Znth (retval - 0 ) keys 0) = ((Znth i values 0) ÷ k_pre ))) (PreH4 : (retval < un)) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= un)) (PreH7 : (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 )) (PreH8 : (0 <= retval)) (PreH9 : (retval <= un)) (PreH10 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH11 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH12 : (a <> 0)) (PreH13 : (vals <> 0)) (PreH14 : (left <> 0)) (PreH15 : (right <> 0)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (1 <= k_pre)) (PreH18 : (k_pre <= 200000)) (PreH19 : (1 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (1 <= un)) (PreH22 : (un <= n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (0 <= ans)) (PreH26 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH27 : ((Zlength (sorted)) = n_pre)) (PreH28 : ((Zlength (keys)) = un)) (PreH29 : ((Zlength (tail)) = (n_pre - un ))) (PreH30 : ((Zlength (left_data)) = un)) (PreH31 : ((Zlength (right_data)) = un)) (PreH32 : (Permutation values sorted )) (PreH33 : (increasing sorted )) (PreH34 : (UniqueKeys sorted keys )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH36 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH37 : (0 <= ix)) (PreH38 : (ix < un)) (PreH39 : (KeyAt keys (Znth i values 0) ix )) (PreH40 : (CountingState k_pre values i keys left_data right_data ans )) (PreH41 : (1 <= (Znth ix right_data 0))) (PreH42 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH43 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH44 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.seg vals 0 un keys )
  **  ((( &( "ri" ) )) # Int  |-> retval_2)
  **  ((( &( "li" ) )) # Int  |-> retval)
  **  (Int64Array.full a n_pre values )
  **  ((( &( "hi" ) )) # Int64  |-> ((Znth i values 0) * k_pre ))
  **  ((( &( "lo" ) )) # Int64  |-> ((Znth i values 0) ÷ k_pre ))
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  ((( &( "ix" ) )) # Int  |-> ix)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
|--
  “ ((ans + ((Znth retval left_data 0) * (Znth retval_2 (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) 0) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (ans + ((Znth retval left_data 0) * (Znth retval_2 (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) 0) ) )) ”
) \/
(
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth (retval_2 - 0 ) keys 0) = ((Znth i values 0) * k_pre ))) (PreH2 : (retval_2 < un)) (PreH3 : ((Znth (retval - 0 ) keys 0) = ((Znth i values 0) ÷ k_pre ))) (PreH4 : (retval < un)) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= un)) (PreH7 : (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 )) (PreH8 : (0 <= retval)) (PreH9 : (retval <= un)) (PreH10 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH11 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH12 : (a <> 0)) (PreH13 : (vals <> 0)) (PreH14 : (left <> 0)) (PreH15 : (right <> 0)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (1 <= k_pre)) (PreH18 : (k_pre <= 200000)) (PreH19 : (1 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (1 <= un)) (PreH22 : (un <= n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (0 <= ans)) (PreH26 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH27 : ((Zlength (sorted)) = n_pre)) (PreH28 : ((Zlength (keys)) = un)) (PreH29 : ((Zlength (tail)) = (n_pre - un ))) (PreH30 : ((Zlength (left_data)) = un)) (PreH31 : ((Zlength (right_data)) = un)) (PreH32 : (Permutation values sorted )) (PreH33 : (increasing sorted )) (PreH34 : (UniqueKeys sorted keys )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH36 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH37 : (0 <= ix)) (PreH38 : (ix < un)) (PreH39 : (KeyAt keys (Znth i values 0) ix )) (PreH40 : (CountingState k_pre values i keys left_data right_data ans )) (PreH41 : (1 <= (Znth ix right_data 0))) (PreH42 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH43 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH44 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.seg vals 0 un keys )
  **  ((( &( "ri" ) )) # Int  |-> retval_2)
  **  ((( &( "li" ) )) # Int  |-> retval)
  **  (Int64Array.full a n_pre values )
  **  ((( &( "hi" ) )) # Int64  |-> ((Znth i values 0) * k_pre ))
  **  ((( &( "lo" ) )) # Int64  |-> ((Znth i values 0) ÷ k_pre ))
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  ((( &( "ix" ) )) # Int  |-> ix)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
|--
  “ ((ans + ((Znth retval left_data 0) * (Znth retval_2 (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) 0) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (ans + ((Znth retval left_data 0) * (Znth retval_2 (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) 0) ) )) ”
).

Definition solver_safety_wit_23_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth (retval_2 - 0 ) keys 0) = ((Znth i values 0) * k_pre ))) (PreH2 : (retval_2 < un)) (PreH3 : ((Znth (retval - 0 ) keys 0) = ((Znth i values 0) ÷ k_pre ))) (PreH4 : (retval < un)) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= un)) (PreH7 : (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 )) (PreH8 : (0 <= retval)) (PreH9 : (retval <= un)) (PreH10 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH11 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH12 : (a <> 0)) (PreH13 : (vals <> 0)) (PreH14 : (left <> 0)) (PreH15 : (right <> 0)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (1 <= k_pre)) (PreH18 : (k_pre <= 200000)) (PreH19 : (1 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (1 <= un)) (PreH22 : (un <= n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (0 <= ans)) (PreH26 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH27 : ((Zlength (sorted)) = n_pre)) (PreH28 : ((Zlength (keys)) = un)) (PreH29 : ((Zlength (tail)) = (n_pre - un ))) (PreH30 : ((Zlength (left_data)) = un)) (PreH31 : ((Zlength (right_data)) = un)) (PreH32 : (Permutation values sorted )) (PreH33 : (increasing sorted )) (PreH34 : (UniqueKeys sorted keys )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH36 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH37 : (0 <= ix)) (PreH38 : (ix < un)) (PreH39 : (KeyAt keys (Znth i values 0) ix )) (PreH40 : (CountingState k_pre values i keys left_data right_data ans )) (PreH41 : (1 <= (Znth ix right_data 0))) (PreH42 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH43 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH44 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.seg vals 0 un keys )
  **  ((( &( "ri" ) )) # Int  |-> retval_2)
  **  ((( &( "li" ) )) # Int  |-> retval)
  **  (Int64Array.full a n_pre values )
  **  ((( &( "hi" ) )) # Int64  |-> ((Znth i values 0) * k_pre ))
  **  ((( &( "lo" ) )) # Int64  |-> ((Znth i values 0) ÷ k_pre ))
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  ((( &( "ix" ) )) # Int  |-> ix)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
|--
  “ ((ans + ((Znth retval left_data 0) * (Znth retval_2 (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) 0) ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_23_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth (retval_2 - 0 ) keys 0) = ((Znth i values 0) * k_pre ))) (PreH2 : (retval_2 < un)) (PreH3 : ((Znth (retval - 0 ) keys 0) = ((Znth i values 0) ÷ k_pre ))) (PreH4 : (retval < un)) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= un)) (PreH7 : (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 )) (PreH8 : (0 <= retval)) (PreH9 : (retval <= un)) (PreH10 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH11 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH12 : (a <> 0)) (PreH13 : (vals <> 0)) (PreH14 : (left <> 0)) (PreH15 : (right <> 0)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (1 <= k_pre)) (PreH18 : (k_pre <= 200000)) (PreH19 : (1 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (1 <= un)) (PreH22 : (un <= n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (0 <= ans)) (PreH26 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH27 : ((Zlength (sorted)) = n_pre)) (PreH28 : ((Zlength (keys)) = un)) (PreH29 : ((Zlength (tail)) = (n_pre - un ))) (PreH30 : ((Zlength (left_data)) = un)) (PreH31 : ((Zlength (right_data)) = un)) (PreH32 : (Permutation values sorted )) (PreH33 : (increasing sorted )) (PreH34 : (UniqueKeys sorted keys )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH36 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH37 : (0 <= ix)) (PreH38 : (ix < un)) (PreH39 : (KeyAt keys (Znth i values 0) ix )) (PreH40 : (CountingState k_pre values i keys left_data right_data ans )) (PreH41 : (1 <= (Znth ix right_data 0))) (PreH42 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH43 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH44 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.seg vals 0 un keys )
  **  ((( &( "ri" ) )) # Int  |-> retval_2)
  **  ((( &( "li" ) )) # Int  |-> retval)
  **  (Int64Array.full a n_pre values )
  **  ((( &( "hi" ) )) # Int64  |-> ((Znth i values 0) * k_pre ))
  **  ((( &( "lo" ) )) # Int64  |-> ((Znth i values 0) ÷ k_pre ))
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  ((( &( "ix" ) )) # Int  |-> ix)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
|--
  “ ((INT64_MIN) <= (ans + ((Znth retval left_data 0) * (Znth retval_2 (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) 0) ) )) ”
.

Definition solver_safety_wit_24 := 
(
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth (retval_2 - 0 ) keys 0) = ((Znth i values 0) * k_pre ))) (PreH2 : (retval_2 < un)) (PreH3 : ((Znth (retval - 0 ) keys 0) = ((Znth i values 0) ÷ k_pre ))) (PreH4 : (retval < un)) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= un)) (PreH7 : (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 )) (PreH8 : (0 <= retval)) (PreH9 : (retval <= un)) (PreH10 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH11 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH12 : (a <> 0)) (PreH13 : (vals <> 0)) (PreH14 : (left <> 0)) (PreH15 : (right <> 0)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (1 <= k_pre)) (PreH18 : (k_pre <= 200000)) (PreH19 : (1 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (1 <= un)) (PreH22 : (un <= n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (0 <= ans)) (PreH26 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH27 : ((Zlength (sorted)) = n_pre)) (PreH28 : ((Zlength (keys)) = un)) (PreH29 : ((Zlength (tail)) = (n_pre - un ))) (PreH30 : ((Zlength (left_data)) = un)) (PreH31 : ((Zlength (right_data)) = un)) (PreH32 : (Permutation values sorted )) (PreH33 : (increasing sorted )) (PreH34 : (UniqueKeys sorted keys )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH36 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH37 : (0 <= ix)) (PreH38 : (ix < un)) (PreH39 : (KeyAt keys (Znth i values 0) ix )) (PreH40 : (CountingState k_pre values i keys left_data right_data ans )) (PreH41 : (1 <= (Znth ix right_data 0))) (PreH42 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH43 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH44 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.seg vals 0 un keys )
  **  ((( &( "ri" ) )) # Int  |-> retval_2)
  **  ((( &( "li" ) )) # Int  |-> retval)
  **  (Int64Array.full a n_pre values )
  **  ((( &( "hi" ) )) # Int64  |-> ((Znth i values 0) * k_pre ))
  **  ((( &( "lo" ) )) # Int64  |-> ((Znth i values 0) ÷ k_pre ))
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  ((( &( "ix" ) )) # Int  |-> ix)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
|--
  “ (((Znth retval left_data 0) * (Znth retval_2 (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth retval left_data 0) * (Znth retval_2 (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) 0) )) ”
) \/
(
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth (retval_2 - 0 ) keys 0) = ((Znth i values 0) * k_pre ))) (PreH2 : (retval_2 < un)) (PreH3 : ((Znth (retval - 0 ) keys 0) = ((Znth i values 0) ÷ k_pre ))) (PreH4 : (retval < un)) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= un)) (PreH7 : (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 )) (PreH8 : (0 <= retval)) (PreH9 : (retval <= un)) (PreH10 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH11 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH12 : (a <> 0)) (PreH13 : (vals <> 0)) (PreH14 : (left <> 0)) (PreH15 : (right <> 0)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (1 <= k_pre)) (PreH18 : (k_pre <= 200000)) (PreH19 : (1 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (1 <= un)) (PreH22 : (un <= n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (0 <= ans)) (PreH26 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH27 : ((Zlength (sorted)) = n_pre)) (PreH28 : ((Zlength (keys)) = un)) (PreH29 : ((Zlength (tail)) = (n_pre - un ))) (PreH30 : ((Zlength (left_data)) = un)) (PreH31 : ((Zlength (right_data)) = un)) (PreH32 : (Permutation values sorted )) (PreH33 : (increasing sorted )) (PreH34 : (UniqueKeys sorted keys )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH36 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH37 : (0 <= ix)) (PreH38 : (ix < un)) (PreH39 : (KeyAt keys (Znth i values 0) ix )) (PreH40 : (CountingState k_pre values i keys left_data right_data ans )) (PreH41 : (1 <= (Znth ix right_data 0))) (PreH42 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH43 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH44 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.seg vals 0 un keys )
  **  ((( &( "ri" ) )) # Int  |-> retval_2)
  **  ((( &( "li" ) )) # Int  |-> retval)
  **  (Int64Array.full a n_pre values )
  **  ((( &( "hi" ) )) # Int64  |-> ((Znth i values 0) * k_pre ))
  **  ((( &( "lo" ) )) # Int64  |-> ((Znth i values 0) ÷ k_pre ))
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  ((( &( "ix" ) )) # Int  |-> ix)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
|--
  “ (((Znth retval left_data 0) * (Znth retval_2 (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth retval left_data 0) * (Znth retval_2 (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) 0) )) ”
).

Definition solver_safety_wit_24_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth (retval_2 - 0 ) keys 0) = ((Znth i values 0) * k_pre ))) (PreH2 : (retval_2 < un)) (PreH3 : ((Znth (retval - 0 ) keys 0) = ((Znth i values 0) ÷ k_pre ))) (PreH4 : (retval < un)) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= un)) (PreH7 : (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 )) (PreH8 : (0 <= retval)) (PreH9 : (retval <= un)) (PreH10 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH11 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH12 : (a <> 0)) (PreH13 : (vals <> 0)) (PreH14 : (left <> 0)) (PreH15 : (right <> 0)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (1 <= k_pre)) (PreH18 : (k_pre <= 200000)) (PreH19 : (1 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (1 <= un)) (PreH22 : (un <= n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (0 <= ans)) (PreH26 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH27 : ((Zlength (sorted)) = n_pre)) (PreH28 : ((Zlength (keys)) = un)) (PreH29 : ((Zlength (tail)) = (n_pre - un ))) (PreH30 : ((Zlength (left_data)) = un)) (PreH31 : ((Zlength (right_data)) = un)) (PreH32 : (Permutation values sorted )) (PreH33 : (increasing sorted )) (PreH34 : (UniqueKeys sorted keys )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH36 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH37 : (0 <= ix)) (PreH38 : (ix < un)) (PreH39 : (KeyAt keys (Znth i values 0) ix )) (PreH40 : (CountingState k_pre values i keys left_data right_data ans )) (PreH41 : (1 <= (Znth ix right_data 0))) (PreH42 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH43 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH44 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.seg vals 0 un keys )
  **  ((( &( "ri" ) )) # Int  |-> retval_2)
  **  ((( &( "li" ) )) # Int  |-> retval)
  **  (Int64Array.full a n_pre values )
  **  ((( &( "hi" ) )) # Int64  |-> ((Znth i values 0) * k_pre ))
  **  ((( &( "lo" ) )) # Int64  |-> ((Znth i values 0) ÷ k_pre ))
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  ((( &( "ix" ) )) # Int  |-> ix)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
|--
  “ (((Znth retval left_data 0) * (Znth retval_2 (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_24_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth (retval_2 - 0 ) keys 0) = ((Znth i values 0) * k_pre ))) (PreH2 : (retval_2 < un)) (PreH3 : ((Znth (retval - 0 ) keys 0) = ((Znth i values 0) ÷ k_pre ))) (PreH4 : (retval < un)) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= un)) (PreH7 : (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 )) (PreH8 : (0 <= retval)) (PreH9 : (retval <= un)) (PreH10 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH11 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH12 : (a <> 0)) (PreH13 : (vals <> 0)) (PreH14 : (left <> 0)) (PreH15 : (right <> 0)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (1 <= k_pre)) (PreH18 : (k_pre <= 200000)) (PreH19 : (1 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (1 <= un)) (PreH22 : (un <= n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (0 <= ans)) (PreH26 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH27 : ((Zlength (sorted)) = n_pre)) (PreH28 : ((Zlength (keys)) = un)) (PreH29 : ((Zlength (tail)) = (n_pre - un ))) (PreH30 : ((Zlength (left_data)) = un)) (PreH31 : ((Zlength (right_data)) = un)) (PreH32 : (Permutation values sorted )) (PreH33 : (increasing sorted )) (PreH34 : (UniqueKeys sorted keys )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH36 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH37 : (0 <= ix)) (PreH38 : (ix < un)) (PreH39 : (KeyAt keys (Znth i values 0) ix )) (PreH40 : (CountingState k_pre values i keys left_data right_data ans )) (PreH41 : (1 <= (Znth ix right_data 0))) (PreH42 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH43 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH44 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.seg vals 0 un keys )
  **  ((( &( "ri" ) )) # Int  |-> retval_2)
  **  ((( &( "li" ) )) # Int  |-> retval)
  **  (Int64Array.full a n_pre values )
  **  ((( &( "hi" ) )) # Int64  |-> ((Znth i values 0) * k_pre ))
  **  ((( &( "lo" ) )) # Int64  |-> ((Znth i values 0) ÷ k_pre ))
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  ((( &( "ix" ) )) # Int  |-> ix)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
|--
  “ ((INT64_MIN) <= ((Znth retval left_data 0) * (Znth retval_2 (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) 0) )) ”
.

Definition solver_safety_wit_25 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth (retval_2 - 0 ) keys 0) = ((Znth i values 0) * k_pre ))) (PreH2 : (retval_2 < un)) (PreH3 : ((Znth (retval - 0 ) keys 0) = ((Znth i values 0) ÷ k_pre ))) (PreH4 : (retval < un)) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= un)) (PreH7 : (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 )) (PreH8 : (0 <= retval)) (PreH9 : (retval <= un)) (PreH10 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH11 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH12 : (a <> 0)) (PreH13 : (vals <> 0)) (PreH14 : (left <> 0)) (PreH15 : (right <> 0)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (1 <= k_pre)) (PreH18 : (k_pre <= 200000)) (PreH19 : (1 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (1 <= un)) (PreH22 : (un <= n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (0 <= ans)) (PreH26 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH27 : ((Zlength (sorted)) = n_pre)) (PreH28 : ((Zlength (keys)) = un)) (PreH29 : ((Zlength (tail)) = (n_pre - un ))) (PreH30 : ((Zlength (left_data)) = un)) (PreH31 : ((Zlength (right_data)) = un)) (PreH32 : (Permutation values sorted )) (PreH33 : (increasing sorted )) (PreH34 : (UniqueKeys sorted keys )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH36 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH37 : (0 <= ix)) (PreH38 : (ix < un)) (PreH39 : (KeyAt keys (Znth i values 0) ix )) (PreH40 : (CountingState k_pre values i keys left_data right_data ans )) (PreH41 : (1 <= (Znth ix right_data 0))) (PreH42 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH43 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH44 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full left un left_data )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> (ans + ((Znth retval left_data 0) * (Znth retval_2 (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) 0) ) ))
  **  ((( &( "ix" ) )) # Int  |-> ix)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
|--
  “ (((Znth ix left_data 0) + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ix left_data 0) + 1 )) ”
.

Definition solver_safety_wit_26 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 >= un)) (PreH2 : ((Znth (retval - 0 ) keys 0) = ((Znth i values 0) ÷ k_pre ))) (PreH3 : (retval < un)) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= un)) (PreH6 : (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 )) (PreH7 : (0 <= retval)) (PreH8 : (retval <= un)) (PreH9 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH10 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH11 : (a <> 0)) (PreH12 : (vals <> 0)) (PreH13 : (left <> 0)) (PreH14 : (right <> 0)) (PreH15 : (n_pre = (Zlength (values)))) (PreH16 : (1 <= k_pre)) (PreH17 : (k_pre <= 200000)) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 200000)) (PreH20 : (1 <= un)) (PreH21 : (un <= n_pre)) (PreH22 : (0 <= i)) (PreH23 : (i < n_pre)) (PreH24 : (0 <= ans)) (PreH25 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH26 : ((Zlength (sorted)) = n_pre)) (PreH27 : ((Zlength (keys)) = un)) (PreH28 : ((Zlength (tail)) = (n_pre - un ))) (PreH29 : ((Zlength (left_data)) = un)) (PreH30 : ((Zlength (right_data)) = un)) (PreH31 : (Permutation values sorted )) (PreH32 : (increasing sorted )) (PreH33 : (UniqueKeys sorted keys )) (PreH34 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH35 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH36 : (0 <= ix)) (PreH37 : (ix < un)) (PreH38 : (KeyAt keys (Znth i values 0) ix )) (PreH39 : (CountingState k_pre values i keys left_data right_data ans )) (PreH40 : (1 <= (Znth ix right_data 0))) (PreH41 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH42 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH43 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full left un left_data )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  ((( &( "ix" ) )) # Int  |-> ix)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
|--
  “ (((Znth ix left_data 0) + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ix left_data 0) + 1 )) ”
.

Definition solver_safety_wit_27 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval >= un)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= un)) (PreH4 : (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 )) (PreH5 : (0 <= retval)) (PreH6 : (retval <= un)) (PreH7 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH8 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH9 : (a <> 0)) (PreH10 : (vals <> 0)) (PreH11 : (left <> 0)) (PreH12 : (right <> 0)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : (1 <= k_pre)) (PreH15 : (k_pre <= 200000)) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 200000)) (PreH18 : (1 <= un)) (PreH19 : (un <= n_pre)) (PreH20 : (0 <= i)) (PreH21 : (i < n_pre)) (PreH22 : (0 <= ans)) (PreH23 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH24 : ((Zlength (sorted)) = n_pre)) (PreH25 : ((Zlength (keys)) = un)) (PreH26 : ((Zlength (tail)) = (n_pre - un ))) (PreH27 : ((Zlength (left_data)) = un)) (PreH28 : ((Zlength (right_data)) = un)) (PreH29 : (Permutation values sorted )) (PreH30 : (increasing sorted )) (PreH31 : (UniqueKeys sorted keys )) (PreH32 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH33 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH34 : (0 <= ix)) (PreH35 : (ix < un)) (PreH36 : (KeyAt keys (Znth i values 0) ix )) (PreH37 : (CountingState k_pre values i keys left_data right_data ans )) (PreH38 : (1 <= (Znth ix right_data 0))) (PreH39 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH40 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH41 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full left un left_data )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  ((( &( "ix" ) )) # Int  |-> ix)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
|--
  “ (((Znth ix left_data 0) + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ix left_data 0) + 1 )) ”
.

Definition solver_safety_wit_28 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth (retval - 0 ) keys 0) <> ((Znth i values 0) ÷ k_pre ))) (PreH2 : (retval < un)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= un)) (PreH5 : (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 )) (PreH6 : (0 <= retval)) (PreH7 : (retval <= un)) (PreH8 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH9 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH10 : (a <> 0)) (PreH11 : (vals <> 0)) (PreH12 : (left <> 0)) (PreH13 : (right <> 0)) (PreH14 : (n_pre = (Zlength (values)))) (PreH15 : (1 <= k_pre)) (PreH16 : (k_pre <= 200000)) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 200000)) (PreH19 : (1 <= un)) (PreH20 : (un <= n_pre)) (PreH21 : (0 <= i)) (PreH22 : (i < n_pre)) (PreH23 : (0 <= ans)) (PreH24 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH25 : ((Zlength (sorted)) = n_pre)) (PreH26 : ((Zlength (keys)) = un)) (PreH27 : ((Zlength (tail)) = (n_pre - un ))) (PreH28 : ((Zlength (left_data)) = un)) (PreH29 : ((Zlength (right_data)) = un)) (PreH30 : (Permutation values sorted )) (PreH31 : (increasing sorted )) (PreH32 : (UniqueKeys sorted keys )) (PreH33 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH34 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH35 : (0 <= ix)) (PreH36 : (ix < un)) (PreH37 : (KeyAt keys (Znth i values 0) ix )) (PreH38 : (CountingState k_pre values i keys left_data right_data ans )) (PreH39 : (1 <= (Znth ix right_data 0))) (PreH40 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH41 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH42 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full left un left_data )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  ((( &( "ix" ) )) # Int  |-> ix)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
|--
  “ (((Znth ix left_data 0) + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ix left_data 0) + 1 )) ”
.

Definition solver_safety_wit_29 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth (retval_2 - 0 ) keys 0) <> ((Znth i values 0) * k_pre ))) (PreH2 : (retval_2 < un)) (PreH3 : ((Znth (retval - 0 ) keys 0) = ((Znth i values 0) ÷ k_pre ))) (PreH4 : (retval < un)) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= un)) (PreH7 : (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 )) (PreH8 : (0 <= retval)) (PreH9 : (retval <= un)) (PreH10 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH11 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH12 : (a <> 0)) (PreH13 : (vals <> 0)) (PreH14 : (left <> 0)) (PreH15 : (right <> 0)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (1 <= k_pre)) (PreH18 : (k_pre <= 200000)) (PreH19 : (1 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (1 <= un)) (PreH22 : (un <= n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (0 <= ans)) (PreH26 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH27 : ((Zlength (sorted)) = n_pre)) (PreH28 : ((Zlength (keys)) = un)) (PreH29 : ((Zlength (tail)) = (n_pre - un ))) (PreH30 : ((Zlength (left_data)) = un)) (PreH31 : ((Zlength (right_data)) = un)) (PreH32 : (Permutation values sorted )) (PreH33 : (increasing sorted )) (PreH34 : (UniqueKeys sorted keys )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH36 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH37 : (0 <= ix)) (PreH38 : (ix < un)) (PreH39 : (KeyAt keys (Znth i values 0) ix )) (PreH40 : (CountingState k_pre values i keys left_data right_data ans )) (PreH41 : (1 <= (Znth ix right_data 0))) (PreH42 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH43 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH44 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full left un left_data )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  ((( &( "ix" ) )) # Int  |-> ix)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
|--
  “ (((Znth ix left_data 0) + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ix left_data 0) + 1 )) ”
.

Definition solver_safety_wit_30 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (PreH1 : (((Znth i values 0) % ( k_pre ) ) <> 0)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (left <> 0)) (PreH5 : (right <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (1 <= un)) (PreH12 : (un <= n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= ans)) (PreH16 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH17 : ((Zlength (sorted)) = n_pre)) (PreH18 : ((Zlength (keys)) = un)) (PreH19 : ((Zlength (tail)) = (n_pre - un ))) (PreH20 : ((Zlength (left_data)) = un)) (PreH21 : ((Zlength (right_data)) = un)) (PreH22 : (Permutation values sorted )) (PreH23 : (increasing sorted )) (PreH24 : (UniqueKeys sorted keys )) (PreH25 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH26 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH27 : (0 <= ix)) (PreH28 : (ix < un)) (PreH29 : (KeyAt keys (Znth i values 0) ix )) (PreH30 : (CountingState k_pre values i keys left_data right_data ans )) (PreH31 : (1 <= (Znth ix right_data 0))) (PreH32 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH33 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH34 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full left un left_data )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  ((( &( "ix" ) )) # Int  |-> ix)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
|--
  “ (((Znth ix left_data 0) + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ix left_data 0) + 1 )) ”
.

Definition solver_safety_wit_31 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth (retval_2 - 0 ) keys 0) = ((Znth i values 0) * k_pre ))) (PreH2 : (retval_2 < un)) (PreH3 : ((Znth (retval - 0 ) keys 0) = ((Znth i values 0) ÷ k_pre ))) (PreH4 : (retval < un)) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= un)) (PreH7 : (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 )) (PreH8 : (0 <= retval)) (PreH9 : (retval <= un)) (PreH10 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH11 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH12 : (a <> 0)) (PreH13 : (vals <> 0)) (PreH14 : (left <> 0)) (PreH15 : (right <> 0)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (1 <= k_pre)) (PreH18 : (k_pre <= 200000)) (PreH19 : (1 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (1 <= un)) (PreH22 : (un <= n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (0 <= ans)) (PreH26 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH27 : ((Zlength (sorted)) = n_pre)) (PreH28 : ((Zlength (keys)) = un)) (PreH29 : ((Zlength (tail)) = (n_pre - un ))) (PreH30 : ((Zlength (left_data)) = un)) (PreH31 : ((Zlength (right_data)) = un)) (PreH32 : (Permutation values sorted )) (PreH33 : (increasing sorted )) (PreH34 : (UniqueKeys sorted keys )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH36 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH37 : (0 <= ix)) (PreH38 : (ix < un)) (PreH39 : (KeyAt keys (Znth i values 0) ix )) (PreH40 : (CountingState k_pre values i keys left_data right_data ans )) (PreH41 : (1 <= (Znth ix right_data 0))) (PreH42 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH43 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH44 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full left un (replace_Znth (ix) (((Znth ix left_data 0) + 1 )) (left_data)) )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> (ans + ((Znth retval left_data 0) * (Znth retval_2 (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) 0) ) ))
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_32 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 >= un)) (PreH2 : ((Znth (retval - 0 ) keys 0) = ((Znth i values 0) ÷ k_pre ))) (PreH3 : (retval < un)) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= un)) (PreH6 : (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 )) (PreH7 : (0 <= retval)) (PreH8 : (retval <= un)) (PreH9 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH10 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH11 : (a <> 0)) (PreH12 : (vals <> 0)) (PreH13 : (left <> 0)) (PreH14 : (right <> 0)) (PreH15 : (n_pre = (Zlength (values)))) (PreH16 : (1 <= k_pre)) (PreH17 : (k_pre <= 200000)) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 200000)) (PreH20 : (1 <= un)) (PreH21 : (un <= n_pre)) (PreH22 : (0 <= i)) (PreH23 : (i < n_pre)) (PreH24 : (0 <= ans)) (PreH25 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH26 : ((Zlength (sorted)) = n_pre)) (PreH27 : ((Zlength (keys)) = un)) (PreH28 : ((Zlength (tail)) = (n_pre - un ))) (PreH29 : ((Zlength (left_data)) = un)) (PreH30 : ((Zlength (right_data)) = un)) (PreH31 : (Permutation values sorted )) (PreH32 : (increasing sorted )) (PreH33 : (UniqueKeys sorted keys )) (PreH34 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH35 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH36 : (0 <= ix)) (PreH37 : (ix < un)) (PreH38 : (KeyAt keys (Znth i values 0) ix )) (PreH39 : (CountingState k_pre values i keys left_data right_data ans )) (PreH40 : (1 <= (Znth ix right_data 0))) (PreH41 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH42 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH43 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full left un (replace_Znth (ix) (((Znth ix left_data 0) + 1 )) (left_data)) )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_33 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval >= un)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= un)) (PreH4 : (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 )) (PreH5 : (0 <= retval)) (PreH6 : (retval <= un)) (PreH7 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH8 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH9 : (a <> 0)) (PreH10 : (vals <> 0)) (PreH11 : (left <> 0)) (PreH12 : (right <> 0)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : (1 <= k_pre)) (PreH15 : (k_pre <= 200000)) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 200000)) (PreH18 : (1 <= un)) (PreH19 : (un <= n_pre)) (PreH20 : (0 <= i)) (PreH21 : (i < n_pre)) (PreH22 : (0 <= ans)) (PreH23 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH24 : ((Zlength (sorted)) = n_pre)) (PreH25 : ((Zlength (keys)) = un)) (PreH26 : ((Zlength (tail)) = (n_pre - un ))) (PreH27 : ((Zlength (left_data)) = un)) (PreH28 : ((Zlength (right_data)) = un)) (PreH29 : (Permutation values sorted )) (PreH30 : (increasing sorted )) (PreH31 : (UniqueKeys sorted keys )) (PreH32 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH33 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH34 : (0 <= ix)) (PreH35 : (ix < un)) (PreH36 : (KeyAt keys (Znth i values 0) ix )) (PreH37 : (CountingState k_pre values i keys left_data right_data ans )) (PreH38 : (1 <= (Znth ix right_data 0))) (PreH39 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH40 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH41 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full left un (replace_Znth (ix) (((Znth ix left_data 0) + 1 )) (left_data)) )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_34 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth (retval - 0 ) keys 0) <> ((Znth i values 0) ÷ k_pre ))) (PreH2 : (retval < un)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= un)) (PreH5 : (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 )) (PreH6 : (0 <= retval)) (PreH7 : (retval <= un)) (PreH8 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH9 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH10 : (a <> 0)) (PreH11 : (vals <> 0)) (PreH12 : (left <> 0)) (PreH13 : (right <> 0)) (PreH14 : (n_pre = (Zlength (values)))) (PreH15 : (1 <= k_pre)) (PreH16 : (k_pre <= 200000)) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 200000)) (PreH19 : (1 <= un)) (PreH20 : (un <= n_pre)) (PreH21 : (0 <= i)) (PreH22 : (i < n_pre)) (PreH23 : (0 <= ans)) (PreH24 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH25 : ((Zlength (sorted)) = n_pre)) (PreH26 : ((Zlength (keys)) = un)) (PreH27 : ((Zlength (tail)) = (n_pre - un ))) (PreH28 : ((Zlength (left_data)) = un)) (PreH29 : ((Zlength (right_data)) = un)) (PreH30 : (Permutation values sorted )) (PreH31 : (increasing sorted )) (PreH32 : (UniqueKeys sorted keys )) (PreH33 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH34 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH35 : (0 <= ix)) (PreH36 : (ix < un)) (PreH37 : (KeyAt keys (Znth i values 0) ix )) (PreH38 : (CountingState k_pre values i keys left_data right_data ans )) (PreH39 : (1 <= (Znth ix right_data 0))) (PreH40 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH41 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH42 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full left un (replace_Znth (ix) (((Znth ix left_data 0) + 1 )) (left_data)) )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_35 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth (retval_2 - 0 ) keys 0) <> ((Znth i values 0) * k_pre ))) (PreH2 : (retval_2 < un)) (PreH3 : ((Znth (retval - 0 ) keys 0) = ((Znth i values 0) ÷ k_pre ))) (PreH4 : (retval < un)) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= un)) (PreH7 : (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 )) (PreH8 : (0 <= retval)) (PreH9 : (retval <= un)) (PreH10 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH11 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH12 : (a <> 0)) (PreH13 : (vals <> 0)) (PreH14 : (left <> 0)) (PreH15 : (right <> 0)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (1 <= k_pre)) (PreH18 : (k_pre <= 200000)) (PreH19 : (1 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (1 <= un)) (PreH22 : (un <= n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (0 <= ans)) (PreH26 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH27 : ((Zlength (sorted)) = n_pre)) (PreH28 : ((Zlength (keys)) = un)) (PreH29 : ((Zlength (tail)) = (n_pre - un ))) (PreH30 : ((Zlength (left_data)) = un)) (PreH31 : ((Zlength (right_data)) = un)) (PreH32 : (Permutation values sorted )) (PreH33 : (increasing sorted )) (PreH34 : (UniqueKeys sorted keys )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH36 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH37 : (0 <= ix)) (PreH38 : (ix < un)) (PreH39 : (KeyAt keys (Znth i values 0) ix )) (PreH40 : (CountingState k_pre values i keys left_data right_data ans )) (PreH41 : (1 <= (Znth ix right_data 0))) (PreH42 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH43 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH44 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full left un (replace_Znth (ix) (((Znth ix left_data 0) + 1 )) (left_data)) )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_36 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (PreH1 : (((Znth i values 0) % ( k_pre ) ) <> 0)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (left <> 0)) (PreH5 : (right <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (1 <= un)) (PreH12 : (un <= n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= ans)) (PreH16 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH17 : ((Zlength (sorted)) = n_pre)) (PreH18 : ((Zlength (keys)) = un)) (PreH19 : ((Zlength (tail)) = (n_pre - un ))) (PreH20 : ((Zlength (left_data)) = un)) (PreH21 : ((Zlength (right_data)) = un)) (PreH22 : (Permutation values sorted )) (PreH23 : (increasing sorted )) (PreH24 : (UniqueKeys sorted keys )) (PreH25 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH26 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH27 : (0 <= ix)) (PreH28 : (ix < un)) (PreH29 : (KeyAt keys (Znth i values 0) ix )) (PreH30 : (CountingState k_pre values i keys left_data right_data ans )) (PreH31 : (1 <= (Znth ix right_data 0))) (PreH32 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH33 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH34 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full left un (replace_Znth (ix) (((Znth ix left_data 0) + 1 )) (left_data)) )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 200000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> (((-1000000000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (values)))) ,
  (Int64Array.undef_full retval_2 n_pre )
  **  (Int64Array.undef_full retval n_pre )
  **  (Int64Array.full input_pre n_pre values )
|--
  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ”
  &&  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg retval 0 0 (sublist (0) (0) (values)) )
  **  (Int64Array.undef_seg retval 0 n_pre )
  **  (Int64Array.seg retval_2 0 0 (sublist (0) (0) (values)) )
  **  (Int64Array.undef_seg retval_2 0 n_pre )
) \/
(
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 200000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> (((-1000000000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (values)))) ,
  TT && emp 
|--
  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ ((sublist (0) (0) (values)) = (@nil Z)) ” 
  &&  “ ((sublist (0) (0) (values)) = (@nil Z)) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 200000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> (((-1000000000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (values)))) ,
  forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 200000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> (((-1000000000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (values)))) ,
  ((sublist (0) (0) (values)) = (@nil Z))
.

Definition solver_entail_wit_1_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 200000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 200000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> (((-1000000000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (values)))) ,
  ((sublist (0) (0) (values)) = (@nil Z))
.

Definition solver_entail_wit_2 := 
(
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (i: Z) (vals: Z) (a: Z) (PreH1 : (i < n_pre)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 200000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) ,
  (Int64Array.seg vals 0 (i + 1 ) (app ((sublist (0) (i) (values))) ((cons ((Znth i values 0)) ((@nil Z))))) )
  **  (Int64Array.undef_seg vals (i + 1 ) n_pre )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg a 0 (i + 1 ) (app ((sublist (0) (i) (values))) ((cons ((Znth i values 0)) ((@nil Z))))) )
  **  (Int64Array.undef_seg a (i + 1 ) n_pre )
|--
  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg a 0 (i + 1 ) (sublist (0) ((i + 1 )) (values)) )
  **  (Int64Array.undef_seg a (i + 1 ) n_pre )
  **  (Int64Array.seg vals 0 (i + 1 ) (sublist (0) ((i + 1 )) (values)) )
  **  (Int64Array.undef_seg vals (i + 1 ) n_pre )
) \/
(
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (i: Z) (vals: Z) (a: Z) (PreH1 : (i < n_pre)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 200000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) ,
  TT && emp 
|--
  “ ((app ((sublist (0) (i) (values))) ((cons ((Znth i values 0)) ((@nil Z))))) = (sublist (0) ((i + 1 )) (values))) ” 
  &&  “ ((app ((sublist (0) (i) (values))) ((cons ((Znth i values 0)) ((@nil Z))))) = (sublist (0) ((i + 1 )) (values))) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (i: Z) (vals: Z) (a: Z) (PreH1 : (i < n_pre)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 200000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) ,
  ((app ((sublist (0) (i) (values))) ((cons ((Znth i values 0)) ((@nil Z))))) = (sublist (0) ((i + 1 )) (values)))
.

Definition solver_entail_wit_2_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (i: Z) (vals: Z) (a: Z) (PreH1 : (i < n_pre)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 200000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) ,
  ((app ((sublist (0) (i) (values))) ((cons ((Znth i values 0)) ((@nil Z))))) = (sublist (0) ((i + 1 )) (values)))
.

Definition solver_entail_wit_3 := 
(
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (i: Z) (vals: Z) (a: Z) (PreH1 : (i >= n_pre)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 200000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((-1000000000) <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) ,
  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg a 0 i (sublist (0) (i) (values)) )
  **  (Int64Array.undef_seg a i n_pre )
  **  (Int64Array.seg vals 0 i (sublist (0) (i) (values)) )
  **  (Int64Array.undef_seg vals i n_pre )
|--
  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full vals n_pre values )
) \/
(
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (i: Z) (vals: Z) (a: Z) (PreH1 : (i >= n_pre)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 200000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((-1000000000) <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) ,
  (Int64Array.seg a 0 i (sublist (0) (i) (values)) )
  **  (Int64Array.seg vals 0 i (sublist (0) (i) (values)) )
|--
  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  (Int64Array.full a n_pre values )
  **  (Int64Array.full vals n_pre values )
).

Definition solver_entail_wit_3_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (i: Z) (vals: Z) (a: Z) (PreH1 : (i >= n_pre)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 200000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((-1000000000) <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) ,
  (Int64Array.seg a 0 i (sublist (0) (i) (values)) )
  **  (Int64Array.seg vals 0 i (sublist (0) (i) (values)) )
|--
  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
.

Definition solver_entail_wit_3_split_goal_spatial := 
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (i: Z) (vals: Z) (a: Z) (PreH1 : (i >= n_pre)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 200000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((-1000000000) <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) ,
  (Int64Array.seg a 0 i (sublist (0) (i) (values)) )
  **  (Int64Array.seg vals 0 i (sublist (0) (i) (values)) )
|--
  (Int64Array.full a n_pre values )
  **  (Int64Array.full vals n_pre values )
.

Definition solver_entail_wit_4 := 
(
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (a: Z) (vals: Z) (sorted_2: (@list Z)) (PreH1 : (Permutation values sorted_2 )) (PreH2 : (increasing sorted_2 )) (PreH3 : ((Zlength (sorted_2)) = n_pre)) (PreH4 : (a <> 0)) (PreH5 : (vals <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((-1000000000) <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) ,
  (Int64Array.full vals n_pre sorted_2 )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
|--
  EX (storage: (@list Z))  (sorted: (@list Z)) ,
  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (storage)) = n_pre) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (CompressionState sorted 0 0 storage ) ”
  &&  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full vals n_pre storage )
) \/
(
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (a: Z) (vals: Z) (sorted_2: (@list Z)) (PreH1 : (Permutation values sorted_2 )) (PreH2 : (increasing sorted_2 )) (PreH3 : ((Zlength (sorted_2)) = n_pre)) (PreH4 : (a <> 0)) (PreH5 : (vals <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((-1000000000) <= (Znth j_2 values 0)) /\ ((Znth j_2 values 0) <= 1000000000)))) ,
  TT && emp 
|--
  EX (sorted: (@list Z)) ,
  “ ((Zlength (sorted)) = (Zlength (sorted_2))) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (Zlength (sorted_2))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (CompressionState sorted 0 0 sorted_2 ) ”
  &&  emp
).

Definition solver_entail_wit_5_1 := 
(
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (un: Z) (i: Z) (storage_2: (@list Z)) (sorted_2: (@list Z)) (vals: Z) (a: Z) (PreH1 : (i = 0)) (PreH2 : (i < n_pre)) (PreH3 : (a <> 0)) (PreH4 : (vals <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 200000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH11 : ((Zlength (sorted_2)) = n_pre)) (PreH12 : ((Zlength (storage_2)) = n_pre)) (PreH13 : (Permutation values sorted_2 )) (PreH14 : (increasing sorted_2 )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= un)) (PreH18 : (un <= i)) (PreH19 : (CompressionState sorted_2 i un storage_2 )) ,
  (Int64Array.full vals n_pre (replace_Znth (un) ((Znth i storage_2 0)) (storage_2)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
|--
  EX (storage: (@list Z))  (sorted: (@list Z)) ,
  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (storage)) = n_pre) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (un + 1 )) ” 
  &&  “ ((un + 1 ) <= (i + 1 )) ” 
  &&  “ (CompressionState sorted (i + 1 ) (un + 1 ) storage ) ”
  &&  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full vals n_pre storage )
) \/
(
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (un: Z) (i: Z) (storage_2: (@list Z)) (sorted_2: (@list Z)) (vals: Z) (a: Z) (PreH1 : (i = 0)) (PreH2 : (i < n_pre)) (PreH3 : (a <> 0)) (PreH4 : (vals <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 200000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH11 : ((Zlength (sorted_2)) = n_pre)) (PreH12 : ((Zlength (storage_2)) = n_pre)) (PreH13 : (Permutation values sorted_2 )) (PreH14 : (increasing sorted_2 )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= un)) (PreH18 : (un <= i)) (PreH19 : (CompressionState sorted_2 i un storage_2 )) ,
  TT && emp 
|--
  EX (sorted: (@list Z)) ,
  “ ((Zlength (sorted)) = (Zlength (values))) ” 
  &&  “ ((Zlength ((replace_Znth (un) ((Znth 0 storage_2 0)) (storage_2)))) = (Zlength (values))) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (0 <= (0 + 1 )) ” 
  &&  “ ((0 + 1 ) <= (Zlength (values))) ” 
  &&  “ (0 <= (un + 1 )) ” 
  &&  “ ((un + 1 ) <= (0 + 1 )) ” 
  &&  “ (CompressionState sorted (0 + 1 ) (un + 1 ) (replace_Znth (un) ((Znth 0 storage_2 0)) (storage_2)) ) ”
  &&  emp
).

Definition solver_entail_wit_5_2 := 
(
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (un: Z) (i: Z) (storage_2: (@list Z)) (sorted_2: (@list Z)) (vals: Z) (a: Z) (PreH1 : ((Znth i storage_2 0) <> (Znth (i - 1 ) storage_2 0))) (PreH2 : (i <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (a <> 0)) (PreH5 : (vals <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH12 : ((Zlength (sorted_2)) = n_pre)) (PreH13 : ((Zlength (storage_2)) = n_pre)) (PreH14 : (Permutation values sorted_2 )) (PreH15 : (increasing sorted_2 )) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= un)) (PreH19 : (un <= i)) (PreH20 : (CompressionState sorted_2 i un storage_2 )) ,
  (Int64Array.full vals n_pre (replace_Znth (un) ((Znth i storage_2 0)) (storage_2)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
|--
  EX (storage: (@list Z))  (sorted: (@list Z)) ,
  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (storage)) = n_pre) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (un + 1 )) ” 
  &&  “ ((un + 1 ) <= (i + 1 )) ” 
  &&  “ (CompressionState sorted (i + 1 ) (un + 1 ) storage ) ”
  &&  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full vals n_pre storage )
) \/
(
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (un: Z) (i: Z) (storage_2: (@list Z)) (sorted_2: (@list Z)) (vals: Z) (a: Z) (PreH1 : ((Znth i storage_2 0) <> (Znth (i - 1 ) storage_2 0))) (PreH2 : (i <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (a <> 0)) (PreH5 : (vals <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH12 : ((Zlength (sorted_2)) = n_pre)) (PreH13 : ((Zlength (storage_2)) = n_pre)) (PreH14 : (Permutation values sorted_2 )) (PreH15 : (increasing sorted_2 )) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= un)) (PreH19 : (un <= i)) (PreH20 : (CompressionState sorted_2 i un storage_2 )) ,
  TT && emp 
|--
  EX (sorted: (@list Z)) ,
  “ ((Zlength (sorted)) = (Zlength (values))) ” 
  &&  “ ((Zlength ((replace_Znth (un) ((Znth i storage_2 0)) (storage_2)))) = (Zlength (values))) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (values))) ” 
  &&  “ (0 <= (un + 1 )) ” 
  &&  “ ((un + 1 ) <= (i + 1 )) ” 
  &&  “ (CompressionState sorted (i + 1 ) (un + 1 ) (replace_Znth (un) ((Znth i storage_2 0)) (storage_2)) ) ”
  &&  emp
).

Definition solver_entail_wit_5_3 := 
(
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (un: Z) (i: Z) (storage_2: (@list Z)) (sorted_2: (@list Z)) (vals: Z) (a: Z) (PreH1 : ((Znth i storage_2 0) = (Znth (i - 1 ) storage_2 0))) (PreH2 : (i <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (a <> 0)) (PreH5 : (vals <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH12 : ((Zlength (sorted_2)) = n_pre)) (PreH13 : ((Zlength (storage_2)) = n_pre)) (PreH14 : (Permutation values sorted_2 )) (PreH15 : (increasing sorted_2 )) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= un)) (PreH19 : (un <= i)) (PreH20 : (CompressionState sorted_2 i un storage_2 )) ,
  (Int64Array.full vals n_pre storage_2 )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
|--
  EX (storage: (@list Z))  (sorted: (@list Z)) ,
  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (storage)) = n_pre) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= un) ” 
  &&  “ (un <= (i + 1 )) ” 
  &&  “ (CompressionState sorted (i + 1 ) un storage ) ”
  &&  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full vals n_pre storage )
) \/
(
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (un: Z) (i: Z) (storage_2: (@list Z)) (sorted_2: (@list Z)) (vals: Z) (a: Z) (PreH1 : ((Znth i storage_2 0) = (Znth (i - 1 ) storage_2 0))) (PreH2 : (i <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (a <> 0)) (PreH5 : (vals <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH12 : ((Zlength (sorted_2)) = n_pre)) (PreH13 : ((Zlength (storage_2)) = n_pre)) (PreH14 : (Permutation values sorted_2 )) (PreH15 : (increasing sorted_2 )) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= un)) (PreH19 : (un <= i)) (PreH20 : (CompressionState sorted_2 i un storage_2 )) ,
  TT && emp 
|--
  EX (sorted: (@list Z)) ,
  “ ((Zlength (sorted)) = (Zlength (values))) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (values))) ” 
  &&  “ (un <= (i + 1 )) ” 
  &&  “ (CompressionState sorted (i + 1 ) un storage_2 ) ”
  &&  emp
).

Definition solver_entail_wit_6 := 
(
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (un: Z) (i: Z) (storage: (@list Z)) (sorted_2: (@list Z)) (vals: Z) (a: Z) (PreH1 : (i >= n_pre)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 200000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < n_pre)) -> (((-1000000000) <= (Znth j_3 values 0)) /\ ((Znth j_3 values 0) <= 1000000000)))) (PreH10 : ((Zlength (sorted_2)) = n_pre)) (PreH11 : ((Zlength (storage)) = n_pre)) (PreH12 : (Permutation values sorted_2 )) (PreH13 : (increasing sorted_2 )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= un)) (PreH17 : (un <= i)) (PreH18 : (CompressionState sorted_2 i un storage )) ,
  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full vals n_pre storage )
|--
  EX (tail: (@list Z))  (keys: (@list Z))  (sorted: (@list Z)) ,
  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ”
  &&  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
) \/
(
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (un: Z) (i: Z) (storage: (@list Z)) (sorted_2: (@list Z)) (vals: Z) (a: Z) (PreH1 : (i >= n_pre)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 200000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < n_pre)) -> (((-1000000000) <= (Znth j_3 values 0)) /\ ((Znth j_3 values 0) <= 1000000000)))) (PreH10 : ((Zlength (sorted_2)) = n_pre)) (PreH11 : ((Zlength (storage)) = n_pre)) (PreH12 : (Permutation values sorted_2 )) (PreH13 : (increasing sorted_2 )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= un)) (PreH17 : (un <= i)) (PreH18 : (CompressionState sorted_2 i un storage )) ,
  (Int64Array.full vals n_pre storage )
|--
  EX (tail: (@list Z))  (keys: (@list Z))  (sorted: (@list Z)) ,
  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ”
  &&  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
).

Definition solver_entail_wit_7 := 
(
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted_2: (@list Z)) (keys_2: (@list Z)) (tail_2: (@list Z)) (a: Z) (vals: Z) (un: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (a <> 0)) (PreH4 : (vals <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 200000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : (1 <= un)) (PreH11 : (un <= n_pre)) (PreH12 : ((Zlength (sorted_2)) = n_pre)) (PreH13 : ((Zlength (keys_2)) = un)) (PreH14 : ((Zlength (tail_2)) = (n_pre - un ))) (PreH15 : (Permutation values sorted_2 )) (PreH16 : (increasing sorted_2 )) (PreH17 : (UniqueKeys sorted_2 keys_2 )) (PreH18 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < n_pre)) -> (((-1000000000) <= (Znth j_4 values 0)) /\ ((Znth j_4 values 0) <= 1000000000)))) (PreH19 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < un)) -> (((-1000000000) <= (Znth j_5 keys_2 0)) /\ ((Znth j_5 keys_2 0) <= 1000000000)))) ,
  (Int64Array.full retval_2 un (repeat_Z (0) (un)) )
  **  (Int64Array.full retval un (repeat_Z (0) (un)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys_2 )
  **  (Int64Array.seg vals un n_pre tail_2 )
|--
  EX (right_data: (@list Z))  (left_data: (@list Z))  (tail: (@list Z))  (keys: (@list Z))  (sorted: (@list Z)) ,
  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (RightBuildState values 0 keys right_data ) ” 
  &&  “ (left_data = (repeat_Z (0) (un))) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 right_data 0)) /\ ((Znth j_3 right_data 0) <= 0))) ”
  &&  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full retval un left_data )
  **  (Int64Array.full retval_2 un right_data )
) \/
(
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (sorted_2: (@list Z)) (keys_2: (@list Z)) (tail_2: (@list Z)) (a: Z) (vals: Z) (un: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (a <> 0)) (PreH4 : (vals <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 200000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : (1 <= un)) (PreH11 : (un <= n_pre)) (PreH12 : ((Zlength (sorted_2)) = n_pre)) (PreH13 : ((Zlength (keys_2)) = un)) (PreH14 : ((Zlength (tail_2)) = (n_pre - un ))) (PreH15 : (Permutation values sorted_2 )) (PreH16 : (increasing sorted_2 )) (PreH17 : (UniqueKeys sorted_2 keys_2 )) (PreH18 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < n_pre)) -> (((-1000000000) <= (Znth j_4 values 0)) /\ ((Znth j_4 values 0) <= 1000000000)))) (PreH19 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < un)) -> (((-1000000000) <= (Znth j_5 keys_2 0)) /\ ((Znth j_5 keys_2 0) <= 1000000000)))) ,
  TT && emp 
|--
  EX (sorted: (@list Z)) ,
  “ ((Zlength (sorted)) = (Zlength (values))) ” 
  &&  “ ((Zlength ((repeat_Z (0) ((Zlength (keys_2)))))) = (Zlength (keys_2))) ” 
  &&  “ ((Zlength ((repeat_Z (0) ((Zlength (keys_2)))))) = (Zlength (keys_2))) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys_2 ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (Zlength (values))) ” 
  &&  “ (RightBuildState values 0 keys_2 (repeat_Z (0) ((Zlength (keys_2)))) ) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (Zlength (keys_2)))) -> ((0 <= (Znth j_3 (repeat_Z (0) ((Zlength (keys_2)))) 0)) /\ ((Znth j_3 (repeat_Z (0) ((Zlength (keys_2)))) 0) <= 0))) ”
  &&  emp
).

Definition solver_entail_wit_8 := 
(
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (i: Z) (right_data_2: (@list Z)) (left_data_2: (@list Z)) (tail_2: (@list Z)) (keys_2: (@list Z)) (sorted_2: (@list Z)) (un: Z) (right: Z) (left: Z) (vals: Z) (a: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= un)) (PreH3 : (LowerBoundResult keys_2 (Znth i values 0) retval )) (PreH4 : (i < n_pre)) (PreH5 : (a <> 0)) (PreH6 : (vals <> 0)) (PreH7 : (left <> 0)) (PreH8 : (right <> 0)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (1 <= k_pre)) (PreH11 : (k_pre <= 200000)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (1 <= un)) (PreH15 : (un <= n_pre)) (PreH16 : ((Zlength (sorted_2)) = n_pre)) (PreH17 : ((Zlength (keys_2)) = un)) (PreH18 : ((Zlength (tail_2)) = (n_pre - un ))) (PreH19 : ((Zlength (left_data_2)) = un)) (PreH20 : ((Zlength (right_data_2)) = un)) (PreH21 : (Permutation values sorted_2 )) (PreH22 : (increasing sorted_2 )) (PreH23 : (UniqueKeys sorted_2 keys_2 )) (PreH24 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < n_pre)) -> (((-1000000000) <= (Znth j_4 values 0)) /\ ((Znth j_4 values 0) <= 1000000000)))) (PreH25 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < un)) -> (((-1000000000) <= (Znth j_5 keys_2 0)) /\ ((Znth j_5 keys_2 0) <= 1000000000)))) (PreH26 : (0 <= i)) (PreH27 : (i <= n_pre)) (PreH28 : (RightBuildState values i keys_2 right_data_2 )) (PreH29 : (left_data_2 = (repeat_Z (0) (un)))) (PreH30 : forall (j_6: Z) , (((0 <= j_6) /\ (j_6 < un)) -> ((0 <= (Znth j_6 right_data_2 0)) /\ ((Znth j_6 right_data_2 0) <= i)))) ,
  (Int64Array.seg vals 0 un keys_2 )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail_2 )
  **  (Int64Array.full left un left_data_2 )
  **  (Int64Array.full right un right_data_2 )
|--
  EX (right_data: (@list Z))  (left_data: (@list Z))  (tail: (@list Z))  (keys: (@list Z))  (sorted: (@list Z)) ,
  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < un) ” 
  &&  “ (KeyAt keys (Znth i values 0) retval ) ” 
  &&  “ (RightBuildState values i keys right_data ) ” 
  &&  “ (left_data = (repeat_Z (0) (un))) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 right_data 0)) /\ ((Znth j_3 right_data 0) <= i))) ”
  &&  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.full right un right_data )
) \/
(
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (i: Z) (right_data_2: (@list Z)) (left_data_2: (@list Z)) (tail_2: (@list Z)) (keys_2: (@list Z)) (sorted_2: (@list Z)) (un: Z) (right: Z) (left: Z) (vals: Z) (a: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= un)) (PreH3 : (LowerBoundResult keys_2 (Znth i values 0) retval )) (PreH4 : (i < n_pre)) (PreH5 : (a <> 0)) (PreH6 : (vals <> 0)) (PreH7 : (left <> 0)) (PreH8 : (right <> 0)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (1 <= k_pre)) (PreH11 : (k_pre <= 200000)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (1 <= un)) (PreH15 : (un <= n_pre)) (PreH16 : ((Zlength (sorted_2)) = n_pre)) (PreH17 : ((Zlength (keys_2)) = un)) (PreH18 : ((Zlength (tail_2)) = (n_pre - un ))) (PreH19 : ((Zlength (left_data_2)) = un)) (PreH20 : ((Zlength (right_data_2)) = un)) (PreH21 : (Permutation values sorted_2 )) (PreH22 : (increasing sorted_2 )) (PreH23 : (UniqueKeys sorted_2 keys_2 )) (PreH24 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < n_pre)) -> (((-1000000000) <= (Znth j_4 values 0)) /\ ((Znth j_4 values 0) <= 1000000000)))) (PreH25 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < un)) -> (((-1000000000) <= (Znth j_5 keys_2 0)) /\ ((Znth j_5 keys_2 0) <= 1000000000)))) (PreH26 : (0 <= i)) (PreH27 : (i <= n_pre)) (PreH28 : (RightBuildState values i keys_2 right_data_2 )) (PreH29 : (left_data_2 = (repeat_Z (0) (un)))) (PreH30 : forall (j_6: Z) , (((0 <= j_6) /\ (j_6 < un)) -> ((0 <= (Znth j_6 right_data_2 0)) /\ ((Znth j_6 right_data_2 0) <= i)))) ,
  TT && emp 
|--
  EX (sorted: (@list Z)) ,
  “ ((Zlength (sorted)) = (Zlength (values))) ” 
  &&  “ ((Zlength ((repeat_Z (0) ((Zlength (keys_2)))))) = (Zlength (keys_2))) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys_2 ) ” 
  &&  “ (retval < (Zlength (keys_2))) ” 
  &&  “ (KeyAt keys_2 (Znth i values 0) retval ) ”
  &&  emp
).

Definition solver_entail_wit_9 := 
(
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted_2: (@list Z)) (keys_2: (@list Z)) (tail_2: (@list Z)) (left_data_2: (@list Z)) (right_data_2: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (index: Z) (PreH1 : (a <> 0)) (PreH2 : (vals <> 0)) (PreH3 : (left <> 0)) (PreH4 : (right <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 200000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : (1 <= un)) (PreH11 : (un <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((Zlength (sorted_2)) = n_pre)) (PreH15 : ((Zlength (keys_2)) = un)) (PreH16 : ((Zlength (tail_2)) = (n_pre - un ))) (PreH17 : ((Zlength (left_data_2)) = un)) (PreH18 : ((Zlength (right_data_2)) = un)) (PreH19 : (Permutation values sorted_2 )) (PreH20 : (increasing sorted_2 )) (PreH21 : (UniqueKeys sorted_2 keys_2 )) (PreH22 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < n_pre)) -> (((-1000000000) <= (Znth j_4 values 0)) /\ ((Znth j_4 values 0) <= 1000000000)))) (PreH23 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < un)) -> (((-1000000000) <= (Znth j_5 keys_2 0)) /\ ((Znth j_5 keys_2 0) <= 1000000000)))) (PreH24 : (0 <= index)) (PreH25 : (index < un)) (PreH26 : (KeyAt keys_2 (Znth i values 0) index )) (PreH27 : (RightBuildState values i keys_2 right_data_2 )) (PreH28 : (left_data_2 = (repeat_Z (0) (un)))) (PreH29 : forall (j_6: Z) , (((0 <= j_6) /\ (j_6 < un)) -> ((0 <= (Znth j_6 right_data_2 0)) /\ ((Znth j_6 right_data_2 0) <= i)))) ,
  (Int64Array.full right un (replace_Znth (index) (((Znth index right_data_2 0) + 1 )) (right_data_2)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys_2 )
  **  (Int64Array.seg vals un n_pre tail_2 )
  **  (Int64Array.full left un left_data_2 )
|--
  EX (right_data: (@list Z))  (left_data: (@list Z))  (tail: (@list Z))  (keys: (@list Z))  (sorted: (@list Z)) ,
  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (RightBuildState values (i + 1 ) keys right_data ) ” 
  &&  “ (left_data = (repeat_Z (0) (un))) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 right_data 0)) /\ ((Znth j_3 right_data 0) <= (i + 1 )))) ”
  &&  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.full right un right_data )
) \/
(
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (sorted_2: (@list Z)) (keys_2: (@list Z)) (tail_2: (@list Z)) (left_data_2: (@list Z)) (right_data_2: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (index: Z) (PreH1 : (a <> 0)) (PreH2 : (vals <> 0)) (PreH3 : (left <> 0)) (PreH4 : (right <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 200000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : (1 <= un)) (PreH11 : (un <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((Zlength (sorted_2)) = n_pre)) (PreH15 : ((Zlength (keys_2)) = un)) (PreH16 : ((Zlength (tail_2)) = (n_pre - un ))) (PreH17 : ((Zlength (left_data_2)) = un)) (PreH18 : ((Zlength (right_data_2)) = un)) (PreH19 : (Permutation values sorted_2 )) (PreH20 : (increasing sorted_2 )) (PreH21 : (UniqueKeys sorted_2 keys_2 )) (PreH22 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < n_pre)) -> (((-1000000000) <= (Znth j_4 values 0)) /\ ((Znth j_4 values 0) <= 1000000000)))) (PreH23 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < un)) -> (((-1000000000) <= (Znth j_5 keys_2 0)) /\ ((Znth j_5 keys_2 0) <= 1000000000)))) (PreH24 : (0 <= index)) (PreH25 : (index < un)) (PreH26 : (KeyAt keys_2 (Znth i values 0) index )) (PreH27 : (RightBuildState values i keys_2 right_data_2 )) (PreH28 : (left_data_2 = (repeat_Z (0) (un)))) (PreH29 : forall (j_6: Z) , (((0 <= j_6) /\ (j_6 < un)) -> ((0 <= (Znth j_6 right_data_2 0)) /\ ((Znth j_6 right_data_2 0) <= i)))) ,
  TT && emp 
|--
  EX (sorted: (@list Z)) ,
  “ ((Zlength (sorted)) = (Zlength (values))) ” 
  &&  “ ((Zlength ((repeat_Z (0) ((Zlength (keys_2)))))) = (Zlength (keys_2))) ” 
  &&  “ ((Zlength ((replace_Znth (index) (((Znth index right_data_2 0) + 1 )) (right_data_2)))) = (Zlength (keys_2))) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys_2 ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (values))) ” 
  &&  “ (RightBuildState values (i + 1 ) keys_2 (replace_Znth (index) (((Znth index right_data_2 0) + 1 )) (right_data_2)) ) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (Zlength (keys_2)))) -> ((0 <= (Znth j_3 (replace_Znth (index) (((Znth index right_data_2 0) + 1 )) (right_data_2)) 0)) /\ ((Znth j_3 (replace_Znth (index) (((Znth index right_data_2 0) + 1 )) (right_data_2)) 0) <= (i + 1 )))) ”
  &&  emp
).

Definition solver_entail_wit_10 := 
(
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (i: Z) (right_data_2: (@list Z)) (left_data_2: (@list Z)) (tail_2: (@list Z)) (keys_2: (@list Z)) (sorted_2: (@list Z)) (un: Z) (right: Z) (left: Z) (vals: Z) (a: Z) (PreH1 : (i >= n_pre)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (left <> 0)) (PreH5 : (right <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (1 <= un)) (PreH12 : (un <= n_pre)) (PreH13 : ((Zlength (sorted_2)) = n_pre)) (PreH14 : ((Zlength (keys_2)) = un)) (PreH15 : ((Zlength (tail_2)) = (n_pre - un ))) (PreH16 : ((Zlength (left_data_2)) = un)) (PreH17 : ((Zlength (right_data_2)) = un)) (PreH18 : (Permutation values sorted_2 )) (PreH19 : (increasing sorted_2 )) (PreH20 : (UniqueKeys sorted_2 keys_2 )) (PreH21 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < n_pre)) -> (((-1000000000) <= (Znth j_5 values 0)) /\ ((Znth j_5 values 0) <= 1000000000)))) (PreH22 : forall (j_6: Z) , (((0 <= j_6) /\ (j_6 < un)) -> (((-1000000000) <= (Znth j_6 keys_2 0)) /\ ((Znth j_6 keys_2 0) <= 1000000000)))) (PreH23 : (0 <= i)) (PreH24 : (i <= n_pre)) (PreH25 : (RightBuildState values i keys_2 right_data_2 )) (PreH26 : (left_data_2 = (repeat_Z (0) (un)))) (PreH27 : forall (j_7: Z) , (((0 <= j_7) /\ (j_7 < un)) -> ((0 <= (Znth j_7 right_data_2 0)) /\ ((Znth j_7 right_data_2 0) <= i)))) ,
  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys_2 )
  **  (Int64Array.seg vals un n_pre tail_2 )
  **  (Int64Array.full left un left_data_2 )
  **  (Int64Array.full right un right_data_2 )
|--
  EX (right_data: (@list Z))  (left_data: (@list Z))  (tail: (@list Z))  (keys: (@list Z))  (sorted: (@list Z)) ,
  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= ((n_pre * n_pre ) * n_pre )) ” 
  &&  “ (CountingState k_pre values 0 keys left_data right_data 0 ) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= 0))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - 0 )))) ”
  &&  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.full right un right_data )
) \/
(
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (i: Z) (right_data_2: (@list Z)) (left_data_2: (@list Z)) (tail_2: (@list Z)) (keys_2: (@list Z)) (sorted_2: (@list Z)) (un: Z) (right: Z) (left: Z) (vals: Z) (a: Z) (PreH1 : (i >= n_pre)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (left <> 0)) (PreH5 : (right <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (1 <= un)) (PreH12 : (un <= n_pre)) (PreH13 : ((Zlength (sorted_2)) = n_pre)) (PreH14 : ((Zlength (keys_2)) = un)) (PreH15 : ((Zlength (tail_2)) = (n_pre - un ))) (PreH16 : ((Zlength (left_data_2)) = un)) (PreH17 : ((Zlength (right_data_2)) = un)) (PreH18 : (Permutation values sorted_2 )) (PreH19 : (increasing sorted_2 )) (PreH20 : (UniqueKeys sorted_2 keys_2 )) (PreH21 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < n_pre)) -> (((-1000000000) <= (Znth j_5 values 0)) /\ ((Znth j_5 values 0) <= 1000000000)))) (PreH22 : forall (j_6: Z) , (((0 <= j_6) /\ (j_6 < un)) -> (((-1000000000) <= (Znth j_6 keys_2 0)) /\ ((Znth j_6 keys_2 0) <= 1000000000)))) (PreH23 : (0 <= i)) (PreH24 : (i <= n_pre)) (PreH25 : (RightBuildState values i keys_2 right_data_2 )) (PreH26 : (left_data_2 = (repeat_Z (0) (un)))) (PreH27 : forall (j_7: Z) , (((0 <= j_7) /\ (j_7 < un)) -> ((0 <= (Znth j_7 right_data_2 0)) /\ ((Znth j_7 right_data_2 0) <= i)))) ,
  TT && emp 
|--
  EX (sorted: (@list Z)) ,
  “ ((Zlength (sorted)) = (Zlength (values))) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys_2 ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (Zlength (values))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (((Zlength (values)) * (Zlength (values)) ) * (Zlength (values)) )) ” 
  &&  “ (CountingState k_pre values 0 keys_2 (repeat_Z (0) (un)) right_data_2 0 ) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (Zlength (keys_2)))) -> ((0 <= (Znth j_3 (repeat_Z (0) (un)) 0)) /\ ((Znth j_3 (repeat_Z (0) (un)) 0) <= 0))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < (Zlength (keys_2)))) -> ((0 <= (Znth j_4 right_data_2 0)) /\ ((Znth j_4 right_data_2 0) <= ((Zlength (values)) - 0 )))) ”
  &&  emp
).

Definition solver_entail_wit_11 := 
(
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (ans: Z) (i: Z) (right_data_2: (@list Z)) (left_data_2: (@list Z)) (tail_2: (@list Z)) (keys_2: (@list Z)) (sorted_2: (@list Z)) (un: Z) (right: Z) (left: Z) (vals: Z) (a: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= un)) (PreH3 : (LowerBoundResult keys_2 (Znth i values 0) retval )) (PreH4 : (i < n_pre)) (PreH5 : (a <> 0)) (PreH6 : (vals <> 0)) (PreH7 : (left <> 0)) (PreH8 : (right <> 0)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (1 <= k_pre)) (PreH11 : (k_pre <= 200000)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (1 <= un)) (PreH15 : (un <= n_pre)) (PreH16 : ((Zlength (sorted_2)) = n_pre)) (PreH17 : ((Zlength (keys_2)) = un)) (PreH18 : ((Zlength (tail_2)) = (n_pre - un ))) (PreH19 : ((Zlength (left_data_2)) = un)) (PreH20 : ((Zlength (right_data_2)) = un)) (PreH21 : (Permutation values sorted_2 )) (PreH22 : (increasing sorted_2 )) (PreH23 : (UniqueKeys sorted_2 keys_2 )) (PreH24 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < n_pre)) -> (((-1000000000) <= (Znth j_5 values 0)) /\ ((Znth j_5 values 0) <= 1000000000)))) (PreH25 : forall (j_6: Z) , (((0 <= j_6) /\ (j_6 < un)) -> (((-1000000000) <= (Znth j_6 keys_2 0)) /\ ((Znth j_6 keys_2 0) <= 1000000000)))) (PreH26 : (0 <= i)) (PreH27 : (i <= n_pre)) (PreH28 : (0 <= ans)) (PreH29 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH30 : (CountingState k_pre values i keys_2 left_data_2 right_data_2 ans )) (PreH31 : forall (j_7: Z) , (((0 <= j_7) /\ (j_7 < un)) -> ((0 <= (Znth j_7 left_data_2 0)) /\ ((Znth j_7 left_data_2 0) <= i)))) (PreH32 : forall (j_8: Z) , (((0 <= j_8) /\ (j_8 < un)) -> ((0 <= (Znth j_8 right_data_2 0)) /\ ((Znth j_8 right_data_2 0) <= (n_pre - i ))))) ,
  (Int64Array.seg vals 0 un keys_2 )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail_2 )
  **  (Int64Array.full left un left_data_2 )
  **  (Int64Array.full right un right_data_2 )
|--
  EX (right_data: (@list Z))  (left_data: (@list Z))  (tail: (@list Z))  (keys: (@list Z))  (sorted: (@list Z)) ,
  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= ((n_pre * n_pre ) * n_pre )) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < un) ” 
  &&  “ (KeyAt keys (Znth i values 0) retval ) ” 
  &&  “ (CountingState k_pre values i keys left_data right_data ans ) ” 
  &&  “ (1 <= (Znth retval right_data 0)) ” 
  &&  “ ((Znth retval right_data 0) <= (n_pre - i )) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i )))) ”
  &&  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.full right un right_data )
) \/
(
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (ans: Z) (i: Z) (right_data_2: (@list Z)) (left_data_2: (@list Z)) (tail_2: (@list Z)) (keys_2: (@list Z)) (sorted_2: (@list Z)) (un: Z) (right: Z) (left: Z) (vals: Z) (a: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= un)) (PreH3 : (LowerBoundResult keys_2 (Znth i values 0) retval )) (PreH4 : (i < n_pre)) (PreH5 : (a <> 0)) (PreH6 : (vals <> 0)) (PreH7 : (left <> 0)) (PreH8 : (right <> 0)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (1 <= k_pre)) (PreH11 : (k_pre <= 200000)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (1 <= un)) (PreH15 : (un <= n_pre)) (PreH16 : ((Zlength (sorted_2)) = n_pre)) (PreH17 : ((Zlength (keys_2)) = un)) (PreH18 : ((Zlength (tail_2)) = (n_pre - un ))) (PreH19 : ((Zlength (left_data_2)) = un)) (PreH20 : ((Zlength (right_data_2)) = un)) (PreH21 : (Permutation values sorted_2 )) (PreH22 : (increasing sorted_2 )) (PreH23 : (UniqueKeys sorted_2 keys_2 )) (PreH24 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < n_pre)) -> (((-1000000000) <= (Znth j_5 values 0)) /\ ((Znth j_5 values 0) <= 1000000000)))) (PreH25 : forall (j_6: Z) , (((0 <= j_6) /\ (j_6 < un)) -> (((-1000000000) <= (Znth j_6 keys_2 0)) /\ ((Znth j_6 keys_2 0) <= 1000000000)))) (PreH26 : (0 <= i)) (PreH27 : (i <= n_pre)) (PreH28 : (0 <= ans)) (PreH29 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH30 : (CountingState k_pre values i keys_2 left_data_2 right_data_2 ans )) (PreH31 : forall (j_7: Z) , (((0 <= j_7) /\ (j_7 < un)) -> ((0 <= (Znth j_7 left_data_2 0)) /\ ((Znth j_7 left_data_2 0) <= i)))) (PreH32 : forall (j_8: Z) , (((0 <= j_8) /\ (j_8 < un)) -> ((0 <= (Znth j_8 right_data_2 0)) /\ ((Znth j_8 right_data_2 0) <= (n_pre - i ))))) ,
  TT && emp 
|--
  EX (sorted: (@list Z)) ,
  “ ((Zlength (sorted)) = (Zlength (values))) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys_2 ) ” 
  &&  “ (retval < (Zlength (keys_2))) ” 
  &&  “ (KeyAt keys_2 (Znth i values 0) retval ) ” 
  &&  “ (1 <= (Znth retval right_data_2 0)) ” 
  &&  “ ((Znth retval right_data_2 0) <= ((Zlength (values)) - i )) ”
  &&  emp
).

Definition solver_entail_wit_12_1 := 
(
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted_2: (@list Z)) (keys_2: (@list Z)) (tail_2: (@list Z)) (left_data_2: (@list Z)) (right_data_2: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth (retval_2 - 0 ) keys_2 0) = ((Znth i values 0) * k_pre ))) (PreH2 : (retval_2 < un)) (PreH3 : ((Znth (retval - 0 ) keys_2 0) = ((Znth i values 0) ÷ k_pre ))) (PreH4 : (retval < un)) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= un)) (PreH7 : (LowerBoundResult keys_2 ((Znth i values 0) * k_pre ) retval_2 )) (PreH8 : (0 <= retval)) (PreH9 : (retval <= un)) (PreH10 : (LowerBoundResult keys_2 ((Znth i values 0) ÷ k_pre ) retval )) (PreH11 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH12 : (a <> 0)) (PreH13 : (vals <> 0)) (PreH14 : (left <> 0)) (PreH15 : (right <> 0)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (1 <= k_pre)) (PreH18 : (k_pre <= 200000)) (PreH19 : (1 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (1 <= un)) (PreH22 : (un <= n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (0 <= ans)) (PreH26 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH27 : ((Zlength (sorted_2)) = n_pre)) (PreH28 : ((Zlength (keys_2)) = un)) (PreH29 : ((Zlength (tail_2)) = (n_pre - un ))) (PreH30 : ((Zlength (left_data_2)) = un)) (PreH31 : ((Zlength (right_data_2)) = un)) (PreH32 : (Permutation values sorted_2 )) (PreH33 : (increasing sorted_2 )) (PreH34 : (UniqueKeys sorted_2 keys_2 )) (PreH35 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < n_pre)) -> (((-1000000000) <= (Znth j_5 values 0)) /\ ((Znth j_5 values 0) <= 1000000000)))) (PreH36 : forall (j_6: Z) , (((0 <= j_6) /\ (j_6 < un)) -> (((-1000000000) <= (Znth j_6 keys_2 0)) /\ ((Znth j_6 keys_2 0) <= 1000000000)))) (PreH37 : (0 <= ix)) (PreH38 : (ix < un)) (PreH39 : (KeyAt keys_2 (Znth i values 0) ix )) (PreH40 : (CountingState k_pre values i keys_2 left_data_2 right_data_2 ans )) (PreH41 : (1 <= (Znth ix right_data_2 0))) (PreH42 : ((Znth ix right_data_2 0) <= (n_pre - i ))) (PreH43 : forall (j_7: Z) , (((0 <= j_7) /\ (j_7 < un)) -> ((0 <= (Znth j_7 left_data_2 0)) /\ ((Znth j_7 left_data_2 0) <= i)))) (PreH44 : forall (j_8: Z) , (((0 <= j_8) /\ (j_8 < un)) -> ((0 <= (Znth j_8 right_data_2 0)) /\ ((Znth j_8 right_data_2 0) <= (n_pre - i ))))) ,
  (Int64Array.full left un (replace_Znth (ix) (((Znth ix left_data_2 0) + 1 )) (left_data_2)) )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)) )
  **  (Int64Array.seg vals 0 un keys_2 )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail_2 )
|--
  EX (right_data: (@list Z))  (left_data: (@list Z))  (tail: (@list Z))  (keys: (@list Z))  (sorted: (@list Z)) ,
  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (ans + ((Znth retval left_data_2 0) * (Znth retval_2 (replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)) 0) ) )) ” 
  &&  “ ((ans + ((Znth retval left_data_2 0) * (Znth retval_2 (replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)) 0) ) ) <= ((n_pre * n_pre ) * n_pre )) ” 
  &&  “ (CountingState k_pre values (i + 1 ) keys left_data right_data (ans + ((Znth retval left_data_2 0) * (Znth retval_2 (replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)) 0) ) ) ) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= (i + 1 )))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - (i + 1 ) )))) ”
  &&  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.full right un right_data )
) \/
(
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (sorted_2: (@list Z)) (keys_2: (@list Z)) (tail_2: (@list Z)) (left_data_2: (@list Z)) (right_data_2: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth (retval_2 - 0 ) keys_2 0) = ((Znth i values 0) * k_pre ))) (PreH2 : (retval_2 < un)) (PreH3 : ((Znth (retval - 0 ) keys_2 0) = ((Znth i values 0) ÷ k_pre ))) (PreH4 : (retval < un)) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= un)) (PreH7 : (LowerBoundResult keys_2 ((Znth i values 0) * k_pre ) retval_2 )) (PreH8 : (0 <= retval)) (PreH9 : (retval <= un)) (PreH10 : (LowerBoundResult keys_2 ((Znth i values 0) ÷ k_pre ) retval )) (PreH11 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH12 : (a <> 0)) (PreH13 : (vals <> 0)) (PreH14 : (left <> 0)) (PreH15 : (right <> 0)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (1 <= k_pre)) (PreH18 : (k_pre <= 200000)) (PreH19 : (1 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (1 <= un)) (PreH22 : (un <= n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (0 <= ans)) (PreH26 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH27 : ((Zlength (sorted_2)) = n_pre)) (PreH28 : ((Zlength (keys_2)) = un)) (PreH29 : ((Zlength (tail_2)) = (n_pre - un ))) (PreH30 : ((Zlength (left_data_2)) = un)) (PreH31 : ((Zlength (right_data_2)) = un)) (PreH32 : (Permutation values sorted_2 )) (PreH33 : (increasing sorted_2 )) (PreH34 : (UniqueKeys sorted_2 keys_2 )) (PreH35 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < n_pre)) -> (((-1000000000) <= (Znth j_5 values 0)) /\ ((Znth j_5 values 0) <= 1000000000)))) (PreH36 : forall (j_6: Z) , (((0 <= j_6) /\ (j_6 < un)) -> (((-1000000000) <= (Znth j_6 keys_2 0)) /\ ((Znth j_6 keys_2 0) <= 1000000000)))) (PreH37 : (0 <= ix)) (PreH38 : (ix < un)) (PreH39 : (KeyAt keys_2 (Znth i values 0) ix )) (PreH40 : (CountingState k_pre values i keys_2 left_data_2 right_data_2 ans )) (PreH41 : (1 <= (Znth ix right_data_2 0))) (PreH42 : ((Znth ix right_data_2 0) <= (n_pre - i ))) (PreH43 : forall (j_7: Z) , (((0 <= j_7) /\ (j_7 < un)) -> ((0 <= (Znth j_7 left_data_2 0)) /\ ((Znth j_7 left_data_2 0) <= i)))) (PreH44 : forall (j_8: Z) , (((0 <= j_8) /\ (j_8 < un)) -> ((0 <= (Znth j_8 right_data_2 0)) /\ ((Znth j_8 right_data_2 0) <= (n_pre - i ))))) ,
  TT && emp 
|--
  EX (sorted: (@list Z)) ,
  “ ((Zlength (sorted)) = (Zlength (values))) ” 
  &&  “ ((Zlength ((replace_Znth (ix) (((Znth ix left_data_2 0) + 1 )) (left_data_2)))) = (Zlength (keys_2))) ” 
  &&  “ ((Zlength ((replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)))) = (Zlength (keys_2))) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys_2 ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (values))) ” 
  &&  “ (0 <= (ans + ((Znth retval left_data_2 0) * (Znth retval_2 (replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)) 0) ) )) ” 
  &&  “ ((ans + ((Znth retval left_data_2 0) * (Znth retval_2 (replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)) 0) ) ) <= (((Zlength (values)) * (Zlength (values)) ) * (Zlength (values)) )) ” 
  &&  “ (CountingState k_pre values (i + 1 ) keys_2 (replace_Znth (ix) (((Znth ix left_data_2 0) + 1 )) (left_data_2)) (replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)) (ans + ((Znth retval left_data_2 0) * (Znth retval_2 (replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)) 0) ) ) ) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (Zlength (keys_2)))) -> ((0 <= (Znth j_3 (replace_Znth (ix) (((Znth ix left_data_2 0) + 1 )) (left_data_2)) 0)) /\ ((Znth j_3 (replace_Znth (ix) (((Znth ix left_data_2 0) + 1 )) (left_data_2)) 0) <= (i + 1 )))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < (Zlength (keys_2)))) -> ((0 <= (Znth j_4 (replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)) 0)) /\ ((Znth j_4 (replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)) 0) <= ((Zlength (values)) - (i + 1 ) )))) ”
  &&  emp
).

Definition solver_entail_wit_12_2 := 
(
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted_2: (@list Z)) (keys_2: (@list Z)) (tail_2: (@list Z)) (left_data_2: (@list Z)) (right_data_2: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 >= un)) (PreH2 : ((Znth (retval - 0 ) keys_2 0) = ((Znth i values 0) ÷ k_pre ))) (PreH3 : (retval < un)) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= un)) (PreH6 : (LowerBoundResult keys_2 ((Znth i values 0) * k_pre ) retval_2 )) (PreH7 : (0 <= retval)) (PreH8 : (retval <= un)) (PreH9 : (LowerBoundResult keys_2 ((Znth i values 0) ÷ k_pre ) retval )) (PreH10 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH11 : (a <> 0)) (PreH12 : (vals <> 0)) (PreH13 : (left <> 0)) (PreH14 : (right <> 0)) (PreH15 : (n_pre = (Zlength (values)))) (PreH16 : (1 <= k_pre)) (PreH17 : (k_pre <= 200000)) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 200000)) (PreH20 : (1 <= un)) (PreH21 : (un <= n_pre)) (PreH22 : (0 <= i)) (PreH23 : (i < n_pre)) (PreH24 : (0 <= ans)) (PreH25 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH26 : ((Zlength (sorted_2)) = n_pre)) (PreH27 : ((Zlength (keys_2)) = un)) (PreH28 : ((Zlength (tail_2)) = (n_pre - un ))) (PreH29 : ((Zlength (left_data_2)) = un)) (PreH30 : ((Zlength (right_data_2)) = un)) (PreH31 : (Permutation values sorted_2 )) (PreH32 : (increasing sorted_2 )) (PreH33 : (UniqueKeys sorted_2 keys_2 )) (PreH34 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < n_pre)) -> (((-1000000000) <= (Znth j_5 values 0)) /\ ((Znth j_5 values 0) <= 1000000000)))) (PreH35 : forall (j_6: Z) , (((0 <= j_6) /\ (j_6 < un)) -> (((-1000000000) <= (Znth j_6 keys_2 0)) /\ ((Znth j_6 keys_2 0) <= 1000000000)))) (PreH36 : (0 <= ix)) (PreH37 : (ix < un)) (PreH38 : (KeyAt keys_2 (Znth i values 0) ix )) (PreH39 : (CountingState k_pre values i keys_2 left_data_2 right_data_2 ans )) (PreH40 : (1 <= (Znth ix right_data_2 0))) (PreH41 : ((Znth ix right_data_2 0) <= (n_pre - i ))) (PreH42 : forall (j_7: Z) , (((0 <= j_7) /\ (j_7 < un)) -> ((0 <= (Znth j_7 left_data_2 0)) /\ ((Znth j_7 left_data_2 0) <= i)))) (PreH43 : forall (j_8: Z) , (((0 <= j_8) /\ (j_8 < un)) -> ((0 <= (Znth j_8 right_data_2 0)) /\ ((Znth j_8 right_data_2 0) <= (n_pre - i ))))) ,
  (Int64Array.full left un (replace_Znth (ix) (((Znth ix left_data_2 0) + 1 )) (left_data_2)) )
  **  (Int64Array.seg vals 0 un keys_2 )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail_2 )
|--
  EX (right_data: (@list Z))  (left_data: (@list Z))  (tail: (@list Z))  (keys: (@list Z))  (sorted: (@list Z)) ,
  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= ((n_pre * n_pre ) * n_pre )) ” 
  &&  “ (CountingState k_pre values (i + 1 ) keys left_data right_data ans ) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= (i + 1 )))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - (i + 1 ) )))) ”
  &&  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.full right un right_data )
) \/
(
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (sorted_2: (@list Z)) (keys_2: (@list Z)) (tail_2: (@list Z)) (left_data_2: (@list Z)) (right_data_2: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 >= un)) (PreH2 : ((Znth (retval - 0 ) keys_2 0) = ((Znth i values 0) ÷ k_pre ))) (PreH3 : (retval < un)) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= un)) (PreH6 : (LowerBoundResult keys_2 ((Znth i values 0) * k_pre ) retval_2 )) (PreH7 : (0 <= retval)) (PreH8 : (retval <= un)) (PreH9 : (LowerBoundResult keys_2 ((Znth i values 0) ÷ k_pre ) retval )) (PreH10 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH11 : (a <> 0)) (PreH12 : (vals <> 0)) (PreH13 : (left <> 0)) (PreH14 : (right <> 0)) (PreH15 : (n_pre = (Zlength (values)))) (PreH16 : (1 <= k_pre)) (PreH17 : (k_pre <= 200000)) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 200000)) (PreH20 : (1 <= un)) (PreH21 : (un <= n_pre)) (PreH22 : (0 <= i)) (PreH23 : (i < n_pre)) (PreH24 : (0 <= ans)) (PreH25 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH26 : ((Zlength (sorted_2)) = n_pre)) (PreH27 : ((Zlength (keys_2)) = un)) (PreH28 : ((Zlength (tail_2)) = (n_pre - un ))) (PreH29 : ((Zlength (left_data_2)) = un)) (PreH30 : ((Zlength (right_data_2)) = un)) (PreH31 : (Permutation values sorted_2 )) (PreH32 : (increasing sorted_2 )) (PreH33 : (UniqueKeys sorted_2 keys_2 )) (PreH34 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < n_pre)) -> (((-1000000000) <= (Znth j_5 values 0)) /\ ((Znth j_5 values 0) <= 1000000000)))) (PreH35 : forall (j_6: Z) , (((0 <= j_6) /\ (j_6 < un)) -> (((-1000000000) <= (Znth j_6 keys_2 0)) /\ ((Znth j_6 keys_2 0) <= 1000000000)))) (PreH36 : (0 <= ix)) (PreH37 : (ix < un)) (PreH38 : (KeyAt keys_2 (Znth i values 0) ix )) (PreH39 : (CountingState k_pre values i keys_2 left_data_2 right_data_2 ans )) (PreH40 : (1 <= (Znth ix right_data_2 0))) (PreH41 : ((Znth ix right_data_2 0) <= (n_pre - i ))) (PreH42 : forall (j_7: Z) , (((0 <= j_7) /\ (j_7 < un)) -> ((0 <= (Znth j_7 left_data_2 0)) /\ ((Znth j_7 left_data_2 0) <= i)))) (PreH43 : forall (j_8: Z) , (((0 <= j_8) /\ (j_8 < un)) -> ((0 <= (Znth j_8 right_data_2 0)) /\ ((Znth j_8 right_data_2 0) <= (n_pre - i ))))) ,
  TT && emp 
|--
  EX (sorted: (@list Z)) ,
  “ ((Zlength (sorted)) = (Zlength (values))) ” 
  &&  “ ((Zlength ((replace_Znth (ix) (((Znth ix left_data_2 0) + 1 )) (left_data_2)))) = (Zlength (keys_2))) ” 
  &&  “ ((Zlength ((replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)))) = (Zlength (keys_2))) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys_2 ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (values))) ” 
  &&  “ (CountingState k_pre values (i + 1 ) keys_2 (replace_Znth (ix) (((Znth ix left_data_2 0) + 1 )) (left_data_2)) (replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)) ans ) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (Zlength (keys_2)))) -> ((0 <= (Znth j_3 (replace_Znth (ix) (((Znth ix left_data_2 0) + 1 )) (left_data_2)) 0)) /\ ((Znth j_3 (replace_Znth (ix) (((Znth ix left_data_2 0) + 1 )) (left_data_2)) 0) <= (i + 1 )))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < (Zlength (keys_2)))) -> ((0 <= (Znth j_4 (replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)) 0)) /\ ((Znth j_4 (replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)) 0) <= ((Zlength (values)) - (i + 1 ) )))) ”
  &&  emp
).

Definition solver_entail_wit_12_3 := 
(
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted_2: (@list Z)) (keys_2: (@list Z)) (tail_2: (@list Z)) (left_data_2: (@list Z)) (right_data_2: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval >= un)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= un)) (PreH4 : (LowerBoundResult keys_2 ((Znth i values 0) * k_pre ) retval_2 )) (PreH5 : (0 <= retval)) (PreH6 : (retval <= un)) (PreH7 : (LowerBoundResult keys_2 ((Znth i values 0) ÷ k_pre ) retval )) (PreH8 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH9 : (a <> 0)) (PreH10 : (vals <> 0)) (PreH11 : (left <> 0)) (PreH12 : (right <> 0)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : (1 <= k_pre)) (PreH15 : (k_pre <= 200000)) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 200000)) (PreH18 : (1 <= un)) (PreH19 : (un <= n_pre)) (PreH20 : (0 <= i)) (PreH21 : (i < n_pre)) (PreH22 : (0 <= ans)) (PreH23 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH24 : ((Zlength (sorted_2)) = n_pre)) (PreH25 : ((Zlength (keys_2)) = un)) (PreH26 : ((Zlength (tail_2)) = (n_pre - un ))) (PreH27 : ((Zlength (left_data_2)) = un)) (PreH28 : ((Zlength (right_data_2)) = un)) (PreH29 : (Permutation values sorted_2 )) (PreH30 : (increasing sorted_2 )) (PreH31 : (UniqueKeys sorted_2 keys_2 )) (PreH32 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < n_pre)) -> (((-1000000000) <= (Znth j_5 values 0)) /\ ((Znth j_5 values 0) <= 1000000000)))) (PreH33 : forall (j_6: Z) , (((0 <= j_6) /\ (j_6 < un)) -> (((-1000000000) <= (Znth j_6 keys_2 0)) /\ ((Znth j_6 keys_2 0) <= 1000000000)))) (PreH34 : (0 <= ix)) (PreH35 : (ix < un)) (PreH36 : (KeyAt keys_2 (Znth i values 0) ix )) (PreH37 : (CountingState k_pre values i keys_2 left_data_2 right_data_2 ans )) (PreH38 : (1 <= (Znth ix right_data_2 0))) (PreH39 : ((Znth ix right_data_2 0) <= (n_pre - i ))) (PreH40 : forall (j_7: Z) , (((0 <= j_7) /\ (j_7 < un)) -> ((0 <= (Znth j_7 left_data_2 0)) /\ ((Znth j_7 left_data_2 0) <= i)))) (PreH41 : forall (j_8: Z) , (((0 <= j_8) /\ (j_8 < un)) -> ((0 <= (Znth j_8 right_data_2 0)) /\ ((Znth j_8 right_data_2 0) <= (n_pre - i ))))) ,
  (Int64Array.full left un (replace_Znth (ix) (((Znth ix left_data_2 0) + 1 )) (left_data_2)) )
  **  (Int64Array.seg vals 0 un keys_2 )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail_2 )
|--
  EX (right_data: (@list Z))  (left_data: (@list Z))  (tail: (@list Z))  (keys: (@list Z))  (sorted: (@list Z)) ,
  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= ((n_pre * n_pre ) * n_pre )) ” 
  &&  “ (CountingState k_pre values (i + 1 ) keys left_data right_data ans ) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= (i + 1 )))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - (i + 1 ) )))) ”
  &&  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.full right un right_data )
) \/
(
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (sorted_2: (@list Z)) (keys_2: (@list Z)) (tail_2: (@list Z)) (left_data_2: (@list Z)) (right_data_2: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval >= un)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= un)) (PreH4 : (LowerBoundResult keys_2 ((Znth i values 0) * k_pre ) retval_2 )) (PreH5 : (0 <= retval)) (PreH6 : (retval <= un)) (PreH7 : (LowerBoundResult keys_2 ((Znth i values 0) ÷ k_pre ) retval )) (PreH8 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH9 : (a <> 0)) (PreH10 : (vals <> 0)) (PreH11 : (left <> 0)) (PreH12 : (right <> 0)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : (1 <= k_pre)) (PreH15 : (k_pre <= 200000)) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 200000)) (PreH18 : (1 <= un)) (PreH19 : (un <= n_pre)) (PreH20 : (0 <= i)) (PreH21 : (i < n_pre)) (PreH22 : (0 <= ans)) (PreH23 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH24 : ((Zlength (sorted_2)) = n_pre)) (PreH25 : ((Zlength (keys_2)) = un)) (PreH26 : ((Zlength (tail_2)) = (n_pre - un ))) (PreH27 : ((Zlength (left_data_2)) = un)) (PreH28 : ((Zlength (right_data_2)) = un)) (PreH29 : (Permutation values sorted_2 )) (PreH30 : (increasing sorted_2 )) (PreH31 : (UniqueKeys sorted_2 keys_2 )) (PreH32 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < n_pre)) -> (((-1000000000) <= (Znth j_5 values 0)) /\ ((Znth j_5 values 0) <= 1000000000)))) (PreH33 : forall (j_6: Z) , (((0 <= j_6) /\ (j_6 < un)) -> (((-1000000000) <= (Znth j_6 keys_2 0)) /\ ((Znth j_6 keys_2 0) <= 1000000000)))) (PreH34 : (0 <= ix)) (PreH35 : (ix < un)) (PreH36 : (KeyAt keys_2 (Znth i values 0) ix )) (PreH37 : (CountingState k_pre values i keys_2 left_data_2 right_data_2 ans )) (PreH38 : (1 <= (Znth ix right_data_2 0))) (PreH39 : ((Znth ix right_data_2 0) <= (n_pre - i ))) (PreH40 : forall (j_7: Z) , (((0 <= j_7) /\ (j_7 < un)) -> ((0 <= (Znth j_7 left_data_2 0)) /\ ((Znth j_7 left_data_2 0) <= i)))) (PreH41 : forall (j_8: Z) , (((0 <= j_8) /\ (j_8 < un)) -> ((0 <= (Znth j_8 right_data_2 0)) /\ ((Znth j_8 right_data_2 0) <= (n_pre - i ))))) ,
  TT && emp 
|--
  EX (sorted: (@list Z)) ,
  “ ((Zlength (sorted)) = (Zlength (values))) ” 
  &&  “ ((Zlength ((replace_Znth (ix) (((Znth ix left_data_2 0) + 1 )) (left_data_2)))) = (Zlength (keys_2))) ” 
  &&  “ ((Zlength ((replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)))) = (Zlength (keys_2))) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys_2 ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (values))) ” 
  &&  “ (CountingState k_pre values (i + 1 ) keys_2 (replace_Znth (ix) (((Znth ix left_data_2 0) + 1 )) (left_data_2)) (replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)) ans ) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (Zlength (keys_2)))) -> ((0 <= (Znth j_3 (replace_Znth (ix) (((Znth ix left_data_2 0) + 1 )) (left_data_2)) 0)) /\ ((Znth j_3 (replace_Znth (ix) (((Znth ix left_data_2 0) + 1 )) (left_data_2)) 0) <= (i + 1 )))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < (Zlength (keys_2)))) -> ((0 <= (Znth j_4 (replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)) 0)) /\ ((Znth j_4 (replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)) 0) <= ((Zlength (values)) - (i + 1 ) )))) ”
  &&  emp
).

Definition solver_entail_wit_12_4 := 
(
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted_2: (@list Z)) (keys_2: (@list Z)) (tail_2: (@list Z)) (left_data_2: (@list Z)) (right_data_2: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth (retval - 0 ) keys_2 0) <> ((Znth i values 0) ÷ k_pre ))) (PreH2 : (retval < un)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= un)) (PreH5 : (LowerBoundResult keys_2 ((Znth i values 0) * k_pre ) retval_2 )) (PreH6 : (0 <= retval)) (PreH7 : (retval <= un)) (PreH8 : (LowerBoundResult keys_2 ((Znth i values 0) ÷ k_pre ) retval )) (PreH9 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH10 : (a <> 0)) (PreH11 : (vals <> 0)) (PreH12 : (left <> 0)) (PreH13 : (right <> 0)) (PreH14 : (n_pre = (Zlength (values)))) (PreH15 : (1 <= k_pre)) (PreH16 : (k_pre <= 200000)) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 200000)) (PreH19 : (1 <= un)) (PreH20 : (un <= n_pre)) (PreH21 : (0 <= i)) (PreH22 : (i < n_pre)) (PreH23 : (0 <= ans)) (PreH24 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH25 : ((Zlength (sorted_2)) = n_pre)) (PreH26 : ((Zlength (keys_2)) = un)) (PreH27 : ((Zlength (tail_2)) = (n_pre - un ))) (PreH28 : ((Zlength (left_data_2)) = un)) (PreH29 : ((Zlength (right_data_2)) = un)) (PreH30 : (Permutation values sorted_2 )) (PreH31 : (increasing sorted_2 )) (PreH32 : (UniqueKeys sorted_2 keys_2 )) (PreH33 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < n_pre)) -> (((-1000000000) <= (Znth j_5 values 0)) /\ ((Znth j_5 values 0) <= 1000000000)))) (PreH34 : forall (j_6: Z) , (((0 <= j_6) /\ (j_6 < un)) -> (((-1000000000) <= (Znth j_6 keys_2 0)) /\ ((Znth j_6 keys_2 0) <= 1000000000)))) (PreH35 : (0 <= ix)) (PreH36 : (ix < un)) (PreH37 : (KeyAt keys_2 (Znth i values 0) ix )) (PreH38 : (CountingState k_pre values i keys_2 left_data_2 right_data_2 ans )) (PreH39 : (1 <= (Znth ix right_data_2 0))) (PreH40 : ((Znth ix right_data_2 0) <= (n_pre - i ))) (PreH41 : forall (j_7: Z) , (((0 <= j_7) /\ (j_7 < un)) -> ((0 <= (Znth j_7 left_data_2 0)) /\ ((Znth j_7 left_data_2 0) <= i)))) (PreH42 : forall (j_8: Z) , (((0 <= j_8) /\ (j_8 < un)) -> ((0 <= (Znth j_8 right_data_2 0)) /\ ((Znth j_8 right_data_2 0) <= (n_pre - i ))))) ,
  (Int64Array.full left un (replace_Znth (ix) (((Znth ix left_data_2 0) + 1 )) (left_data_2)) )
  **  (Int64Array.seg vals 0 un keys_2 )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail_2 )
|--
  EX (right_data: (@list Z))  (left_data: (@list Z))  (tail: (@list Z))  (keys: (@list Z))  (sorted: (@list Z)) ,
  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= ((n_pre * n_pre ) * n_pre )) ” 
  &&  “ (CountingState k_pre values (i + 1 ) keys left_data right_data ans ) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= (i + 1 )))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - (i + 1 ) )))) ”
  &&  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.full right un right_data )
) \/
(
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (sorted_2: (@list Z)) (keys_2: (@list Z)) (tail_2: (@list Z)) (left_data_2: (@list Z)) (right_data_2: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth (retval - 0 ) keys_2 0) <> ((Znth i values 0) ÷ k_pre ))) (PreH2 : (retval < un)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= un)) (PreH5 : (LowerBoundResult keys_2 ((Znth i values 0) * k_pre ) retval_2 )) (PreH6 : (0 <= retval)) (PreH7 : (retval <= un)) (PreH8 : (LowerBoundResult keys_2 ((Znth i values 0) ÷ k_pre ) retval )) (PreH9 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH10 : (a <> 0)) (PreH11 : (vals <> 0)) (PreH12 : (left <> 0)) (PreH13 : (right <> 0)) (PreH14 : (n_pre = (Zlength (values)))) (PreH15 : (1 <= k_pre)) (PreH16 : (k_pre <= 200000)) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 200000)) (PreH19 : (1 <= un)) (PreH20 : (un <= n_pre)) (PreH21 : (0 <= i)) (PreH22 : (i < n_pre)) (PreH23 : (0 <= ans)) (PreH24 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH25 : ((Zlength (sorted_2)) = n_pre)) (PreH26 : ((Zlength (keys_2)) = un)) (PreH27 : ((Zlength (tail_2)) = (n_pre - un ))) (PreH28 : ((Zlength (left_data_2)) = un)) (PreH29 : ((Zlength (right_data_2)) = un)) (PreH30 : (Permutation values sorted_2 )) (PreH31 : (increasing sorted_2 )) (PreH32 : (UniqueKeys sorted_2 keys_2 )) (PreH33 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < n_pre)) -> (((-1000000000) <= (Znth j_5 values 0)) /\ ((Znth j_5 values 0) <= 1000000000)))) (PreH34 : forall (j_6: Z) , (((0 <= j_6) /\ (j_6 < un)) -> (((-1000000000) <= (Znth j_6 keys_2 0)) /\ ((Znth j_6 keys_2 0) <= 1000000000)))) (PreH35 : (0 <= ix)) (PreH36 : (ix < un)) (PreH37 : (KeyAt keys_2 (Znth i values 0) ix )) (PreH38 : (CountingState k_pre values i keys_2 left_data_2 right_data_2 ans )) (PreH39 : (1 <= (Znth ix right_data_2 0))) (PreH40 : ((Znth ix right_data_2 0) <= (n_pre - i ))) (PreH41 : forall (j_7: Z) , (((0 <= j_7) /\ (j_7 < un)) -> ((0 <= (Znth j_7 left_data_2 0)) /\ ((Znth j_7 left_data_2 0) <= i)))) (PreH42 : forall (j_8: Z) , (((0 <= j_8) /\ (j_8 < un)) -> ((0 <= (Znth j_8 right_data_2 0)) /\ ((Znth j_8 right_data_2 0) <= (n_pre - i ))))) ,
  TT && emp 
|--
  EX (sorted: (@list Z)) ,
  “ ((Zlength (sorted)) = (Zlength (values))) ” 
  &&  “ ((Zlength ((replace_Znth (ix) (((Znth ix left_data_2 0) + 1 )) (left_data_2)))) = (Zlength (keys_2))) ” 
  &&  “ ((Zlength ((replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)))) = (Zlength (keys_2))) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys_2 ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (values))) ” 
  &&  “ (CountingState k_pre values (i + 1 ) keys_2 (replace_Znth (ix) (((Znth ix left_data_2 0) + 1 )) (left_data_2)) (replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)) ans ) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (Zlength (keys_2)))) -> ((0 <= (Znth j_3 (replace_Znth (ix) (((Znth ix left_data_2 0) + 1 )) (left_data_2)) 0)) /\ ((Znth j_3 (replace_Znth (ix) (((Znth ix left_data_2 0) + 1 )) (left_data_2)) 0) <= (i + 1 )))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < (Zlength (keys_2)))) -> ((0 <= (Znth j_4 (replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)) 0)) /\ ((Znth j_4 (replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)) 0) <= ((Zlength (values)) - (i + 1 ) )))) ”
  &&  emp
).

Definition solver_entail_wit_12_5 := 
(
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted_2: (@list Z)) (keys_2: (@list Z)) (tail_2: (@list Z)) (left_data_2: (@list Z)) (right_data_2: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth (retval_2 - 0 ) keys_2 0) <> ((Znth i values 0) * k_pre ))) (PreH2 : (retval_2 < un)) (PreH3 : ((Znth (retval - 0 ) keys_2 0) = ((Znth i values 0) ÷ k_pre ))) (PreH4 : (retval < un)) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= un)) (PreH7 : (LowerBoundResult keys_2 ((Znth i values 0) * k_pre ) retval_2 )) (PreH8 : (0 <= retval)) (PreH9 : (retval <= un)) (PreH10 : (LowerBoundResult keys_2 ((Znth i values 0) ÷ k_pre ) retval )) (PreH11 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH12 : (a <> 0)) (PreH13 : (vals <> 0)) (PreH14 : (left <> 0)) (PreH15 : (right <> 0)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (1 <= k_pre)) (PreH18 : (k_pre <= 200000)) (PreH19 : (1 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (1 <= un)) (PreH22 : (un <= n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (0 <= ans)) (PreH26 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH27 : ((Zlength (sorted_2)) = n_pre)) (PreH28 : ((Zlength (keys_2)) = un)) (PreH29 : ((Zlength (tail_2)) = (n_pre - un ))) (PreH30 : ((Zlength (left_data_2)) = un)) (PreH31 : ((Zlength (right_data_2)) = un)) (PreH32 : (Permutation values sorted_2 )) (PreH33 : (increasing sorted_2 )) (PreH34 : (UniqueKeys sorted_2 keys_2 )) (PreH35 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < n_pre)) -> (((-1000000000) <= (Znth j_5 values 0)) /\ ((Znth j_5 values 0) <= 1000000000)))) (PreH36 : forall (j_6: Z) , (((0 <= j_6) /\ (j_6 < un)) -> (((-1000000000) <= (Znth j_6 keys_2 0)) /\ ((Znth j_6 keys_2 0) <= 1000000000)))) (PreH37 : (0 <= ix)) (PreH38 : (ix < un)) (PreH39 : (KeyAt keys_2 (Znth i values 0) ix )) (PreH40 : (CountingState k_pre values i keys_2 left_data_2 right_data_2 ans )) (PreH41 : (1 <= (Znth ix right_data_2 0))) (PreH42 : ((Znth ix right_data_2 0) <= (n_pre - i ))) (PreH43 : forall (j_7: Z) , (((0 <= j_7) /\ (j_7 < un)) -> ((0 <= (Znth j_7 left_data_2 0)) /\ ((Znth j_7 left_data_2 0) <= i)))) (PreH44 : forall (j_8: Z) , (((0 <= j_8) /\ (j_8 < un)) -> ((0 <= (Znth j_8 right_data_2 0)) /\ ((Znth j_8 right_data_2 0) <= (n_pre - i ))))) ,
  (Int64Array.full left un (replace_Znth (ix) (((Znth ix left_data_2 0) + 1 )) (left_data_2)) )
  **  (Int64Array.seg vals 0 un keys_2 )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail_2 )
|--
  EX (right_data: (@list Z))  (left_data: (@list Z))  (tail: (@list Z))  (keys: (@list Z))  (sorted: (@list Z)) ,
  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= ((n_pre * n_pre ) * n_pre )) ” 
  &&  “ (CountingState k_pre values (i + 1 ) keys left_data right_data ans ) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= (i + 1 )))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - (i + 1 ) )))) ”
  &&  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.full right un right_data )
) \/
(
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (sorted_2: (@list Z)) (keys_2: (@list Z)) (tail_2: (@list Z)) (left_data_2: (@list Z)) (right_data_2: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth (retval_2 - 0 ) keys_2 0) <> ((Znth i values 0) * k_pre ))) (PreH2 : (retval_2 < un)) (PreH3 : ((Znth (retval - 0 ) keys_2 0) = ((Znth i values 0) ÷ k_pre ))) (PreH4 : (retval < un)) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= un)) (PreH7 : (LowerBoundResult keys_2 ((Znth i values 0) * k_pre ) retval_2 )) (PreH8 : (0 <= retval)) (PreH9 : (retval <= un)) (PreH10 : (LowerBoundResult keys_2 ((Znth i values 0) ÷ k_pre ) retval )) (PreH11 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH12 : (a <> 0)) (PreH13 : (vals <> 0)) (PreH14 : (left <> 0)) (PreH15 : (right <> 0)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (1 <= k_pre)) (PreH18 : (k_pre <= 200000)) (PreH19 : (1 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (1 <= un)) (PreH22 : (un <= n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (0 <= ans)) (PreH26 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH27 : ((Zlength (sorted_2)) = n_pre)) (PreH28 : ((Zlength (keys_2)) = un)) (PreH29 : ((Zlength (tail_2)) = (n_pre - un ))) (PreH30 : ((Zlength (left_data_2)) = un)) (PreH31 : ((Zlength (right_data_2)) = un)) (PreH32 : (Permutation values sorted_2 )) (PreH33 : (increasing sorted_2 )) (PreH34 : (UniqueKeys sorted_2 keys_2 )) (PreH35 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < n_pre)) -> (((-1000000000) <= (Znth j_5 values 0)) /\ ((Znth j_5 values 0) <= 1000000000)))) (PreH36 : forall (j_6: Z) , (((0 <= j_6) /\ (j_6 < un)) -> (((-1000000000) <= (Znth j_6 keys_2 0)) /\ ((Znth j_6 keys_2 0) <= 1000000000)))) (PreH37 : (0 <= ix)) (PreH38 : (ix < un)) (PreH39 : (KeyAt keys_2 (Znth i values 0) ix )) (PreH40 : (CountingState k_pre values i keys_2 left_data_2 right_data_2 ans )) (PreH41 : (1 <= (Znth ix right_data_2 0))) (PreH42 : ((Znth ix right_data_2 0) <= (n_pre - i ))) (PreH43 : forall (j_7: Z) , (((0 <= j_7) /\ (j_7 < un)) -> ((0 <= (Znth j_7 left_data_2 0)) /\ ((Znth j_7 left_data_2 0) <= i)))) (PreH44 : forall (j_8: Z) , (((0 <= j_8) /\ (j_8 < un)) -> ((0 <= (Znth j_8 right_data_2 0)) /\ ((Znth j_8 right_data_2 0) <= (n_pre - i ))))) ,
  TT && emp 
|--
  EX (sorted: (@list Z)) ,
  “ ((Zlength (sorted)) = (Zlength (values))) ” 
  &&  “ ((Zlength ((replace_Znth (ix) (((Znth ix left_data_2 0) + 1 )) (left_data_2)))) = (Zlength (keys_2))) ” 
  &&  “ ((Zlength ((replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)))) = (Zlength (keys_2))) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys_2 ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (values))) ” 
  &&  “ (CountingState k_pre values (i + 1 ) keys_2 (replace_Znth (ix) (((Znth ix left_data_2 0) + 1 )) (left_data_2)) (replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)) ans ) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (Zlength (keys_2)))) -> ((0 <= (Znth j_3 (replace_Znth (ix) (((Znth ix left_data_2 0) + 1 )) (left_data_2)) 0)) /\ ((Znth j_3 (replace_Znth (ix) (((Znth ix left_data_2 0) + 1 )) (left_data_2)) 0) <= (i + 1 )))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < (Zlength (keys_2)))) -> ((0 <= (Znth j_4 (replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)) 0)) /\ ((Znth j_4 (replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)) 0) <= ((Zlength (values)) - (i + 1 ) )))) ”
  &&  emp
).

Definition solver_entail_wit_12_6 := 
(
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted_2: (@list Z)) (keys_2: (@list Z)) (tail_2: (@list Z)) (left_data_2: (@list Z)) (right_data_2: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (PreH1 : (((Znth i values 0) % ( k_pre ) ) <> 0)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (left <> 0)) (PreH5 : (right <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (1 <= un)) (PreH12 : (un <= n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= ans)) (PreH16 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH17 : ((Zlength (sorted_2)) = n_pre)) (PreH18 : ((Zlength (keys_2)) = un)) (PreH19 : ((Zlength (tail_2)) = (n_pre - un ))) (PreH20 : ((Zlength (left_data_2)) = un)) (PreH21 : ((Zlength (right_data_2)) = un)) (PreH22 : (Permutation values sorted_2 )) (PreH23 : (increasing sorted_2 )) (PreH24 : (UniqueKeys sorted_2 keys_2 )) (PreH25 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < n_pre)) -> (((-1000000000) <= (Znth j_5 values 0)) /\ ((Znth j_5 values 0) <= 1000000000)))) (PreH26 : forall (j_6: Z) , (((0 <= j_6) /\ (j_6 < un)) -> (((-1000000000) <= (Znth j_6 keys_2 0)) /\ ((Znth j_6 keys_2 0) <= 1000000000)))) (PreH27 : (0 <= ix)) (PreH28 : (ix < un)) (PreH29 : (KeyAt keys_2 (Znth i values 0) ix )) (PreH30 : (CountingState k_pre values i keys_2 left_data_2 right_data_2 ans )) (PreH31 : (1 <= (Znth ix right_data_2 0))) (PreH32 : ((Znth ix right_data_2 0) <= (n_pre - i ))) (PreH33 : forall (j_7: Z) , (((0 <= j_7) /\ (j_7 < un)) -> ((0 <= (Znth j_7 left_data_2 0)) /\ ((Znth j_7 left_data_2 0) <= i)))) (PreH34 : forall (j_8: Z) , (((0 <= j_8) /\ (j_8 < un)) -> ((0 <= (Znth j_8 right_data_2 0)) /\ ((Znth j_8 right_data_2 0) <= (n_pre - i ))))) ,
  (Int64Array.full left un (replace_Znth (ix) (((Znth ix left_data_2 0) + 1 )) (left_data_2)) )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals 0 un keys_2 )
  **  (Int64Array.seg vals un n_pre tail_2 )
|--
  EX (right_data: (@list Z))  (left_data: (@list Z))  (tail: (@list Z))  (keys: (@list Z))  (sorted: (@list Z)) ,
  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= ((n_pre * n_pre ) * n_pre )) ” 
  &&  “ (CountingState k_pre values (i + 1 ) keys left_data right_data ans ) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= (i + 1 )))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - (i + 1 ) )))) ”
  &&  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.full right un right_data )
) \/
(
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (sorted_2: (@list Z)) (keys_2: (@list Z)) (tail_2: (@list Z)) (left_data_2: (@list Z)) (right_data_2: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (PreH1 : (((Znth i values 0) % ( k_pre ) ) <> 0)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (left <> 0)) (PreH5 : (right <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (1 <= un)) (PreH12 : (un <= n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= ans)) (PreH16 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH17 : ((Zlength (sorted_2)) = n_pre)) (PreH18 : ((Zlength (keys_2)) = un)) (PreH19 : ((Zlength (tail_2)) = (n_pre - un ))) (PreH20 : ((Zlength (left_data_2)) = un)) (PreH21 : ((Zlength (right_data_2)) = un)) (PreH22 : (Permutation values sorted_2 )) (PreH23 : (increasing sorted_2 )) (PreH24 : (UniqueKeys sorted_2 keys_2 )) (PreH25 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < n_pre)) -> (((-1000000000) <= (Znth j_5 values 0)) /\ ((Znth j_5 values 0) <= 1000000000)))) (PreH26 : forall (j_6: Z) , (((0 <= j_6) /\ (j_6 < un)) -> (((-1000000000) <= (Znth j_6 keys_2 0)) /\ ((Znth j_6 keys_2 0) <= 1000000000)))) (PreH27 : (0 <= ix)) (PreH28 : (ix < un)) (PreH29 : (KeyAt keys_2 (Znth i values 0) ix )) (PreH30 : (CountingState k_pre values i keys_2 left_data_2 right_data_2 ans )) (PreH31 : (1 <= (Znth ix right_data_2 0))) (PreH32 : ((Znth ix right_data_2 0) <= (n_pre - i ))) (PreH33 : forall (j_7: Z) , (((0 <= j_7) /\ (j_7 < un)) -> ((0 <= (Znth j_7 left_data_2 0)) /\ ((Znth j_7 left_data_2 0) <= i)))) (PreH34 : forall (j_8: Z) , (((0 <= j_8) /\ (j_8 < un)) -> ((0 <= (Znth j_8 right_data_2 0)) /\ ((Znth j_8 right_data_2 0) <= (n_pre - i ))))) ,
  TT && emp 
|--
  EX (sorted: (@list Z)) ,
  “ ((Zlength (sorted)) = (Zlength (values))) ” 
  &&  “ ((Zlength ((replace_Znth (ix) (((Znth ix left_data_2 0) + 1 )) (left_data_2)))) = (Zlength (keys_2))) ” 
  &&  “ ((Zlength ((replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)))) = (Zlength (keys_2))) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys_2 ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (values))) ” 
  &&  “ (CountingState k_pre values (i + 1 ) keys_2 (replace_Znth (ix) (((Znth ix left_data_2 0) + 1 )) (left_data_2)) (replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)) ans ) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (Zlength (keys_2)))) -> ((0 <= (Znth j_3 (replace_Znth (ix) (((Znth ix left_data_2 0) + 1 )) (left_data_2)) 0)) /\ ((Znth j_3 (replace_Znth (ix) (((Znth ix left_data_2 0) + 1 )) (left_data_2)) 0) <= (i + 1 )))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < (Zlength (keys_2)))) -> ((0 <= (Znth j_4 (replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)) 0)) /\ ((Znth j_4 (replace_Znth (ix) (((Znth ix right_data_2 0) - 1 )) (right_data_2)) 0) <= ((Zlength (values)) - (i + 1 ) )))) ”
  &&  emp
).

Definition solver_entail_wit_13 := 
(
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (ans: Z) (i: Z) (right_data_2: (@list Z)) (left_data_2: (@list Z)) (tail_2: (@list Z)) (keys_2: (@list Z)) (sorted: (@list Z)) (un: Z) (right: Z) (left: Z) (vals: Z) (a: Z) (PreH1 : (i >= n_pre)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (left <> 0)) (PreH5 : (right <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (1 <= un)) (PreH12 : (un <= n_pre)) (PreH13 : ((Zlength (sorted)) = n_pre)) (PreH14 : ((Zlength (keys_2)) = un)) (PreH15 : ((Zlength (tail_2)) = (n_pre - un ))) (PreH16 : ((Zlength (left_data_2)) = un)) (PreH17 : ((Zlength (right_data_2)) = un)) (PreH18 : (Permutation values sorted )) (PreH19 : (increasing sorted )) (PreH20 : (UniqueKeys sorted keys_2 )) (PreH21 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH22 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys_2 0)) /\ ((Znth j_2 keys_2 0) <= 1000000000)))) (PreH23 : (0 <= i)) (PreH24 : (i <= n_pre)) (PreH25 : (0 <= ans)) (PreH26 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH27 : (CountingState k_pre values i keys_2 left_data_2 right_data_2 ans )) (PreH28 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data_2 0)) /\ ((Znth j_3 left_data_2 0) <= i)))) (PreH29 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data_2 0)) /\ ((Znth j_4 right_data_2 0) <= (n_pre - i ))))) ,
  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys_2 )
  **  (Int64Array.seg vals un n_pre tail_2 )
  **  (Int64Array.full left un left_data_2 )
  **  (Int64Array.full right un right_data_2 )
|--
  EX (right_data: (@list Z))  (left_data: (@list Z))  (tail: (@list Z))  (keys: (@list Z)) ,
  “ (n_pre = (Zlength (values))) ” 
  &&  “ (Spec k_pre values ans ) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ”
  &&  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full vals n_pre (app (keys) (tail)) )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.full right un right_data )
) \/
(
forall (k_pre: Z) (n_pre: Z) (values: (@list Z)) (ans: Z) (i: Z) (right_data_2: (@list Z)) (left_data_2: (@list Z)) (tail_2: (@list Z)) (keys_2: (@list Z)) (sorted: (@list Z)) (un: Z) (right: Z) (left: Z) (vals: Z) (a: Z) (PreH1 : (i >= n_pre)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (left <> 0)) (PreH5 : (right <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (1 <= un)) (PreH12 : (un <= n_pre)) (PreH13 : ((Zlength (sorted)) = n_pre)) (PreH14 : ((Zlength (keys_2)) = un)) (PreH15 : ((Zlength (tail_2)) = (n_pre - un ))) (PreH16 : ((Zlength (left_data_2)) = un)) (PreH17 : ((Zlength (right_data_2)) = un)) (PreH18 : (Permutation values sorted )) (PreH19 : (increasing sorted )) (PreH20 : (UniqueKeys sorted keys_2 )) (PreH21 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH22 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys_2 0)) /\ ((Znth j_2 keys_2 0) <= 1000000000)))) (PreH23 : (0 <= i)) (PreH24 : (i <= n_pre)) (PreH25 : (0 <= ans)) (PreH26 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH27 : (CountingState k_pre values i keys_2 left_data_2 right_data_2 ans )) (PreH28 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data_2 0)) /\ ((Znth j_3 left_data_2 0) <= i)))) (PreH29 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data_2 0)) /\ ((Znth j_4 right_data_2 0) <= (n_pre - i ))))) ,
  (Int64Array.seg vals 0 un keys_2 )
  **  (Int64Array.seg vals un n_pre tail_2 )
|--
  EX (tail: (@list Z))  (keys: (@list Z)) ,
  “ (n_pre = (Zlength (values))) ” 
  &&  “ (Spec k_pre values ans ) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data_2)) = un) ” 
  &&  “ ((Zlength (right_data_2)) = un) ”
  &&  (Int64Array.full vals n_pre (app (keys) (tail)) )
).

Definition solver_return_wit_1 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (ans: Z) (un: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (Spec k_pre values ans )) (PreH3 : ((Zlength (keys)) = un)) (PreH4 : ((Zlength (tail)) = (n_pre - un ))) (PreH5 : ((Zlength (left_data)) = un)) (PreH6 : ((Zlength (right_data)) = un)) ,
  (Int64Array.full input_pre n_pre values )
|--
  “ (Spec k_pre values ans ) ”
  &&  (Int64Array.full input_pre n_pre values )
.

Definition solver_partial_solve_wit_1_pure := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 200000)) (PreH3 : (1 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> (((-1000000000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH6 : (n_pre = (Zlength (values)))) ,
  ((( &( "a" ) )) # Ptr  |->_)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  (Int64Array.full input_pre n_pre values )
|--
  “ (0 <= n_pre) ” 
  &&  “ ((n_pre * sizeof(INT64) ) = (n_pre * sizeof(INT64) )) ”
.

Definition solver_partial_solve_wit_1_aux := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 200000)) (PreH3 : (1 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> (((-1000000000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH6 : (n_pre = (Zlength (values)))) ,
  (Int64Array.full input_pre n_pre values )
|--
  “ (0 <= n_pre) ” 
  &&  “ ((n_pre * sizeof(INT64) ) = (n_pre * sizeof(INT64) )) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= (Zlength (values))) ” 
  &&  “ ((Zlength (values)) <= 200000) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> (((-1000000000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000))) ” 
  &&  “ (n_pre = (Zlength (values))) ”
  &&  (Int64Array.full input_pre n_pre values )
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2_pure := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 200000)) (PreH4 : (1 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> (((-1000000000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH7 : (n_pre = (Zlength (values)))) ,
  ((( &( "vals" ) )) # Ptr  |->_)
  **  (Int64Array.undef_full retval n_pre )
  **  ((( &( "a" ) )) # Ptr  |-> retval)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  (Int64Array.full input_pre n_pre values )
|--
  “ (0 <= n_pre) ” 
  &&  “ ((n_pre * sizeof(INT64) ) = (n_pre * sizeof(INT64) )) ”
.

Definition solver_partial_solve_wit_2_aux := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 200000)) (PreH4 : (1 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> (((-1000000000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH7 : (n_pre = (Zlength (values)))) ,
  (Int64Array.undef_full retval n_pre )
  **  (Int64Array.full input_pre n_pre values )
|--
  “ (0 <= n_pre) ” 
  &&  “ ((n_pre * sizeof(INT64) ) = (n_pre * sizeof(INT64) )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= (Zlength (values))) ” 
  &&  “ ((Zlength (values)) <= 200000) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> (((-1000000000) <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000))) ” 
  &&  “ (n_pre = (Zlength (values))) ”
  &&  (Int64Array.undef_full retval n_pre )
  **  (Int64Array.full input_pre n_pre values )
.

Definition solver_partial_solve_wit_2 := solver_partial_solve_wit_2_pure -> solver_partial_solve_wit_2_aux.

Definition solver_partial_solve_wit_3 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (i: Z) (vals: Z) (a: Z) (PreH1 : (i < n_pre)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 200000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) ,
  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg a 0 i (sublist (0) (i) (values)) )
  **  (Int64Array.undef_seg a i n_pre )
  **  (Int64Array.seg vals 0 i (sublist (0) (i) (values)) )
  **  (Int64Array.undef_seg vals i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (((input_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.missing_i input_pre i 0 n_pre values )
  **  (Int64Array.seg a 0 i (sublist (0) (i) (values)) )
  **  (Int64Array.undef_seg a i n_pre )
  **  (Int64Array.seg vals 0 i (sublist (0) (i) (values)) )
  **  (Int64Array.undef_seg vals i n_pre )
.

Definition solver_partial_solve_wit_4 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (i: Z) (vals: Z) (a: Z) (PreH1 : (i < n_pre)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 200000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) ,
  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg a 0 i (sublist (0) (i) (values)) )
  **  (Int64Array.undef_seg a i n_pre )
  **  (Int64Array.seg vals 0 i (sublist (0) (i) (values)) )
  **  (Int64Array.undef_seg vals i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (((a + (i * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg a (i + 1 ) n_pre )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg a 0 i (sublist (0) (i) (values)) )
  **  (Int64Array.seg vals 0 i (sublist (0) (i) (values)) )
  **  (Int64Array.undef_seg vals i n_pre )
.

Definition solver_partial_solve_wit_5 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (i: Z) (vals: Z) (a: Z) (PreH1 : (i < n_pre)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 200000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) ,
  (Int64Array.seg a 0 (i + 1 ) (app ((sublist (0) (i) (values))) ((cons ((Znth i values 0)) ((@nil Z))))) )
  **  (Int64Array.undef_seg a (i + 1 ) n_pre )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals 0 i (sublist (0) (i) (values)) )
  **  (Int64Array.undef_seg vals i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (((input_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.missing_i input_pre i 0 n_pre values )
  **  (Int64Array.seg a 0 (i + 1 ) (app ((sublist (0) (i) (values))) ((cons ((Znth i values 0)) ((@nil Z))))) )
  **  (Int64Array.undef_seg a (i + 1 ) n_pre )
  **  (Int64Array.seg vals 0 i (sublist (0) (i) (values)) )
  **  (Int64Array.undef_seg vals i n_pre )
.

Definition solver_partial_solve_wit_6 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (i: Z) (vals: Z) (a: Z) (PreH1 : (i < n_pre)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 200000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) ,
  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg a 0 (i + 1 ) (app ((sublist (0) (i) (values))) ((cons ((Znth i values 0)) ((@nil Z))))) )
  **  (Int64Array.undef_seg a (i + 1 ) n_pre )
  **  (Int64Array.seg vals 0 i (sublist (0) (i) (values)) )
  **  (Int64Array.undef_seg vals i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (((vals + (i * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg vals (i + 1 ) n_pre )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg a 0 (i + 1 ) (app ((sublist (0) (i) (values))) ((cons ((Znth i values 0)) ((@nil Z))))) )
  **  (Int64Array.undef_seg a (i + 1 ) n_pre )
  **  (Int64Array.seg vals 0 i (sublist (0) (i) (values)) )
.

Definition solver_partial_solve_wit_7_pure := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (a: Z) (vals: Z) (PreH1 : (a <> 0)) (PreH2 : (vals <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 200000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) ,
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full vals n_pre values )
|--
  “ (n_pre = (Zlength (values))) ” 
  &&  “ (sizeof(INT64) = sizeof(INT64)) ”
.

Definition solver_partial_solve_wit_7_aux := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (a: Z) (vals: Z) (PreH1 : (a <> 0)) (PreH2 : (vals <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 200000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) ,
  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full vals n_pre values )
|--
  “ (n_pre = (Zlength (values))) ” 
  &&  “ (sizeof(INT64) = sizeof(INT64)) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ”
  &&  (Int64Array.full vals n_pre values )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
.

Definition solver_partial_solve_wit_7 := solver_partial_solve_wit_7_pure -> solver_partial_solve_wit_7_aux.

Definition solver_partial_solve_wit_8 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (un: Z) (i: Z) (storage: (@list Z)) (sorted: (@list Z)) (vals: Z) (a: Z) (PreH1 : (i <> 0)) (PreH2 : (i < n_pre)) (PreH3 : (a <> 0)) (PreH4 : (vals <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 200000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : ((Zlength (storage)) = n_pre)) (PreH13 : (Permutation values sorted )) (PreH14 : (increasing sorted )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= un)) (PreH18 : (un <= i)) (PreH19 : (CompressionState sorted i un storage )) ,
  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full vals n_pre storage )
|--
  “ (i <> 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (storage)) = n_pre) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= un) ” 
  &&  “ (un <= i) ” 
  &&  “ (CompressionState sorted i un storage ) ”
  &&  (((vals + (i * sizeof(INT64)))) # Int64  |-> (Znth i storage 0))
  **  (Int64Array.missing_i vals i 0 n_pre storage )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
.

Definition solver_partial_solve_wit_9 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (un: Z) (i: Z) (storage: (@list Z)) (sorted: (@list Z)) (vals: Z) (a: Z) (PreH1 : (i <> 0)) (PreH2 : (i < n_pre)) (PreH3 : (a <> 0)) (PreH4 : (vals <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 200000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : ((Zlength (storage)) = n_pre)) (PreH13 : (Permutation values sorted )) (PreH14 : (increasing sorted )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= un)) (PreH18 : (un <= i)) (PreH19 : (CompressionState sorted i un storage )) ,
  (Int64Array.full vals n_pre storage )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
|--
  “ (i <> 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (storage)) = n_pre) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= un) ” 
  &&  “ (un <= i) ” 
  &&  “ (CompressionState sorted i un storage ) ”
  &&  (((vals + ((i - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth (i - 1 ) storage 0))
  **  (Int64Array.missing_i vals (i - 1 ) 0 n_pre storage )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
.

Definition solver_partial_solve_wit_10 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (un: Z) (i: Z) (storage: (@list Z)) (sorted: (@list Z)) (vals: Z) (a: Z) (PreH1 : (i = 0)) (PreH2 : (i < n_pre)) (PreH3 : (a <> 0)) (PreH4 : (vals <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 200000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : ((Zlength (storage)) = n_pre)) (PreH13 : (Permutation values sorted )) (PreH14 : (increasing sorted )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= un)) (PreH18 : (un <= i)) (PreH19 : (CompressionState sorted i un storage )) ,
  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full vals n_pre storage )
|--
  “ (i = 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (storage)) = n_pre) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= un) ” 
  &&  “ (un <= i) ” 
  &&  “ (CompressionState sorted i un storage ) ”
  &&  (((vals + (i * sizeof(INT64)))) # Int64  |-> (Znth i storage 0))
  **  (Int64Array.missing_i vals i 0 n_pre storage )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
.

Definition solver_partial_solve_wit_11 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (un: Z) (i: Z) (storage: (@list Z)) (sorted: (@list Z)) (vals: Z) (a: Z) (PreH1 : (i = 0)) (PreH2 : (i < n_pre)) (PreH3 : (a <> 0)) (PreH4 : (vals <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 200000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : ((Zlength (storage)) = n_pre)) (PreH13 : (Permutation values sorted )) (PreH14 : (increasing sorted )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (0 <= un)) (PreH18 : (un <= i)) (PreH19 : (CompressionState sorted i un storage )) ,
  (Int64Array.full vals n_pre storage )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
|--
  “ (i = 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (storage)) = n_pre) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= un) ” 
  &&  “ (un <= i) ” 
  &&  “ (CompressionState sorted i un storage ) ”
  &&  (((vals + (un * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i vals un 0 n_pre storage )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
.

Definition solver_partial_solve_wit_12 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (un: Z) (i: Z) (storage: (@list Z)) (sorted: (@list Z)) (vals: Z) (a: Z) (PreH1 : ((Znth i storage 0) <> (Znth (i - 1 ) storage 0))) (PreH2 : (i <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (a <> 0)) (PreH5 : (vals <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : ((Zlength (storage)) = n_pre)) (PreH14 : (Permutation values sorted )) (PreH15 : (increasing sorted )) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= un)) (PreH19 : (un <= i)) (PreH20 : (CompressionState sorted i un storage )) ,
  (Int64Array.full vals n_pre storage )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
|--
  “ ((Znth i storage 0) <> (Znth (i - 1 ) storage 0)) ” 
  &&  “ (i <> 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (storage)) = n_pre) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= un) ” 
  &&  “ (un <= i) ” 
  &&  “ (CompressionState sorted i un storage ) ”
  &&  (((vals + (i * sizeof(INT64)))) # Int64  |-> (Znth i storage 0))
  **  (Int64Array.missing_i vals i 0 n_pre storage )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
.

Definition solver_partial_solve_wit_13 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (un: Z) (i: Z) (storage: (@list Z)) (sorted: (@list Z)) (vals: Z) (a: Z) (PreH1 : ((Znth i storage 0) <> (Znth (i - 1 ) storage 0))) (PreH2 : (i <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (a <> 0)) (PreH5 : (vals <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : ((Zlength (storage)) = n_pre)) (PreH14 : (Permutation values sorted )) (PreH15 : (increasing sorted )) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= un)) (PreH19 : (un <= i)) (PreH20 : (CompressionState sorted i un storage )) ,
  (Int64Array.full vals n_pre storage )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
|--
  “ ((Znth i storage 0) <> (Znth (i - 1 ) storage 0)) ” 
  &&  “ (i <> 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (storage)) = n_pre) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= un) ” 
  &&  “ (un <= i) ” 
  &&  “ (CompressionState sorted i un storage ) ”
  &&  (((vals + (un * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i vals un 0 n_pre storage )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
.

Definition solver_partial_solve_wit_14_pure := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (a: Z) (vals: Z) (un: Z) (PreH1 : (a <> 0)) (PreH2 : (vals <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 200000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (1 <= un)) (PreH9 : (un <= n_pre)) (PreH10 : ((Zlength (sorted)) = n_pre)) (PreH11 : ((Zlength (keys)) = un)) (PreH12 : ((Zlength (tail)) = (n_pre - un ))) (PreH13 : (Permutation values sorted )) (PreH14 : (increasing sorted )) (PreH15 : (UniqueKeys sorted keys )) (PreH16 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH17 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) ,
  ((( &( "left" ) )) # Ptr  |->_)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
|--
  “ (0 <= un) ” 
  &&  “ (un = un) ” 
  &&  “ (sizeof(INT64) = sizeof(INT64)) ”
.

Definition solver_partial_solve_wit_14_aux := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (a: Z) (vals: Z) (un: Z) (PreH1 : (a <> 0)) (PreH2 : (vals <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 200000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (1 <= un)) (PreH9 : (un <= n_pre)) (PreH10 : ((Zlength (sorted)) = n_pre)) (PreH11 : ((Zlength (keys)) = un)) (PreH12 : ((Zlength (tail)) = (n_pre - un ))) (PreH13 : (Permutation values sorted )) (PreH14 : (increasing sorted )) (PreH15 : (UniqueKeys sorted keys )) (PreH16 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH17 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) ,
  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
|--
  “ (0 <= un) ” 
  &&  “ (un = un) ” 
  &&  “ (sizeof(INT64) = sizeof(INT64)) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ”
  &&  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
.

Definition solver_partial_solve_wit_14 := solver_partial_solve_wit_14_pure -> solver_partial_solve_wit_14_aux.

Definition solver_partial_solve_wit_15_pure := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (a: Z) (vals: Z) (un: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 200000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= un)) (PreH10 : (un <= n_pre)) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : ((Zlength (keys)) = un)) (PreH13 : ((Zlength (tail)) = (n_pre - un ))) (PreH14 : (Permutation values sorted )) (PreH15 : (increasing sorted )) (PreH16 : (UniqueKeys sorted keys )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH18 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) ,
  ((( &( "right" ) )) # Ptr  |->_)
  **  (Int64Array.full retval un (repeat_Z (0) (un)) )
  **  ((( &( "left" ) )) # Ptr  |-> retval)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
|--
  “ (0 <= un) ” 
  &&  “ (un = un) ” 
  &&  “ (sizeof(INT64) = sizeof(INT64)) ”
.

Definition solver_partial_solve_wit_15_aux := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (a: Z) (vals: Z) (un: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 200000)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= un)) (PreH10 : (un <= n_pre)) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : ((Zlength (keys)) = un)) (PreH13 : ((Zlength (tail)) = (n_pre - un ))) (PreH14 : (Permutation values sorted )) (PreH15 : (increasing sorted )) (PreH16 : (UniqueKeys sorted keys )) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH18 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) ,
  (Int64Array.full retval un (repeat_Z (0) (un)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
|--
  “ (0 <= un) ” 
  &&  “ (un = un) ” 
  &&  “ (sizeof(INT64) = sizeof(INT64)) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ”
  &&  (Int64Array.full retval un (repeat_Z (0) (un)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
.

Definition solver_partial_solve_wit_15 := solver_partial_solve_wit_15_pure -> solver_partial_solve_wit_15_aux.

Definition solver_partial_solve_wit_16 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (i: Z) (right_data: (@list Z)) (left_data: (@list Z)) (tail: (@list Z)) (keys: (@list Z)) (sorted: (@list Z)) (un: Z) (right: Z) (left: Z) (vals: Z) (a: Z) (PreH1 : (i < n_pre)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (left <> 0)) (PreH5 : (right <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (1 <= un)) (PreH12 : (un <= n_pre)) (PreH13 : ((Zlength (sorted)) = n_pre)) (PreH14 : ((Zlength (keys)) = un)) (PreH15 : ((Zlength (tail)) = (n_pre - un ))) (PreH16 : ((Zlength (left_data)) = un)) (PreH17 : ((Zlength (right_data)) = un)) (PreH18 : (Permutation values sorted )) (PreH19 : (increasing sorted )) (PreH20 : (UniqueKeys sorted keys )) (PreH21 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH22 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH23 : (0 <= i)) (PreH24 : (i <= n_pre)) (PreH25 : (RightBuildState values i keys right_data )) (PreH26 : (left_data = (repeat_Z (0) (un)))) (PreH27 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 right_data 0)) /\ ((Znth j_3 right_data 0) <= i)))) ,
  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.full right un right_data )
|--
  “ (i < n_pre) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (RightBuildState values i keys right_data ) ” 
  &&  “ (left_data = (repeat_Z (0) (un))) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 right_data 0)) /\ ((Znth j_3 right_data 0) <= i))) ”
  &&  (((a + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.missing_i a i 0 n_pre values )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.full right un right_data )
.

Definition solver_partial_solve_wit_17_pure := 
(
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (i: Z) (right_data: (@list Z)) (left_data: (@list Z)) (tail: (@list Z)) (keys: (@list Z)) (sorted: (@list Z)) (un: Z) (right: Z) (left: Z) (vals: Z) (a: Z) (PreH1 : (i < n_pre)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (left <> 0)) (PreH5 : (right <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (1 <= un)) (PreH12 : (un <= n_pre)) (PreH13 : ((Zlength (sorted)) = n_pre)) (PreH14 : ((Zlength (keys)) = un)) (PreH15 : ((Zlength (tail)) = (n_pre - un ))) (PreH16 : ((Zlength (left_data)) = un)) (PreH17 : ((Zlength (right_data)) = un)) (PreH18 : (Permutation values sorted )) (PreH19 : (increasing sorted )) (PreH20 : (UniqueKeys sorted keys )) (PreH21 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH22 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH23 : (0 <= i)) (PreH24 : (i <= n_pre)) (PreH25 : (RightBuildState values i keys right_data )) (PreH26 : (left_data = (repeat_Z (0) (un)))) (PreH27 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 right_data 0)) /\ ((Znth j_3 right_data 0) <= i)))) ,
  (Int64Array.full a n_pre values )
  **  ((( &( "index" ) )) # Int  |->_)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.full right un right_data )
|--
  “ (un = (Zlength (keys))) ” 
  &&  “ (0 <= un) ” 
  &&  “ (un <= 200000) ” 
  &&  “ (increasing keys ) ”
) \/
(
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (i: Z) (right_data: (@list Z)) (left_data: (@list Z)) (tail: (@list Z)) (keys: (@list Z)) (sorted: (@list Z)) (un: Z) (right: Z) (left: Z) (vals: Z) (a: Z) (PreH1 : (k_pre <= INT64_MAX)) (PreH2 : (k_pre >= INT64_MIN)) (PreH3 : (i <= INT_MAX)) (PreH4 : (un <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (un >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i < n_pre)) (PreH10 : (a <> 0)) (PreH11 : (vals <> 0)) (PreH12 : (left <> 0)) (PreH13 : (right <> 0)) (PreH14 : (n_pre = (Zlength (values)))) (PreH15 : (1 <= k_pre)) (PreH16 : (k_pre <= 200000)) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 200000)) (PreH19 : (1 <= un)) (PreH20 : (un <= n_pre)) (PreH21 : ((Zlength (sorted)) = n_pre)) (PreH22 : ((Zlength (keys)) = un)) (PreH23 : ((Zlength (tail)) = (n_pre - un ))) (PreH24 : ((Zlength (left_data)) = un)) (PreH25 : ((Zlength (right_data)) = un)) (PreH26 : (Permutation values sorted )) (PreH27 : (increasing sorted )) (PreH28 : (UniqueKeys sorted keys )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH31 : (0 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (RightBuildState values i keys right_data )) (PreH34 : (left_data = (repeat_Z (0) (un)))) (PreH35 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 right_data 0)) /\ ((Znth j_3 right_data 0) <= i)))) ,
  (Int64Array.full a n_pre values )
  **  ((( &( "index" ) )) # Int  |->_)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.full right un right_data )
|--
  “ (increasing keys ) ”
).

Definition solver_partial_solve_wit_17_pure_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (i: Z) (right_data: (@list Z)) (left_data: (@list Z)) (tail: (@list Z)) (keys: (@list Z)) (sorted: (@list Z)) (un: Z) (right: Z) (left: Z) (vals: Z) (a: Z) (PreH1 : (k_pre <= INT64_MAX)) (PreH2 : (k_pre >= INT64_MIN)) (PreH3 : (i <= INT_MAX)) (PreH4 : (un <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (un >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i < n_pre)) (PreH10 : (a <> 0)) (PreH11 : (vals <> 0)) (PreH12 : (left <> 0)) (PreH13 : (right <> 0)) (PreH14 : (n_pre = (Zlength (values)))) (PreH15 : (1 <= k_pre)) (PreH16 : (k_pre <= 200000)) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 200000)) (PreH19 : (1 <= un)) (PreH20 : (un <= n_pre)) (PreH21 : ((Zlength (sorted)) = n_pre)) (PreH22 : ((Zlength (keys)) = un)) (PreH23 : ((Zlength (tail)) = (n_pre - un ))) (PreH24 : ((Zlength (left_data)) = un)) (PreH25 : ((Zlength (right_data)) = un)) (PreH26 : (Permutation values sorted )) (PreH27 : (increasing sorted )) (PreH28 : (UniqueKeys sorted keys )) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH31 : (0 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (RightBuildState values i keys right_data )) (PreH34 : (left_data = (repeat_Z (0) (un)))) (PreH35 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 right_data 0)) /\ ((Znth j_3 right_data 0) <= i)))) ,
  (Int64Array.full a n_pre values )
  **  ((( &( "index" ) )) # Int  |->_)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.full right un right_data )
|--
  “ (increasing keys ) ”
.

Definition solver_partial_solve_wit_17_aux := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (i: Z) (right_data: (@list Z)) (left_data: (@list Z)) (tail: (@list Z)) (keys: (@list Z)) (sorted: (@list Z)) (un: Z) (right: Z) (left: Z) (vals: Z) (a: Z) (PreH1 : (i < n_pre)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (left <> 0)) (PreH5 : (right <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (1 <= un)) (PreH12 : (un <= n_pre)) (PreH13 : ((Zlength (sorted)) = n_pre)) (PreH14 : ((Zlength (keys)) = un)) (PreH15 : ((Zlength (tail)) = (n_pre - un ))) (PreH16 : ((Zlength (left_data)) = un)) (PreH17 : ((Zlength (right_data)) = un)) (PreH18 : (Permutation values sorted )) (PreH19 : (increasing sorted )) (PreH20 : (UniqueKeys sorted keys )) (PreH21 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH22 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH23 : (0 <= i)) (PreH24 : (i <= n_pre)) (PreH25 : (RightBuildState values i keys right_data )) (PreH26 : (left_data = (repeat_Z (0) (un)))) (PreH27 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 right_data 0)) /\ ((Znth j_3 right_data 0) <= i)))) ,
  (Int64Array.full a n_pre values )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.full right un right_data )
|--
  “ (un = (Zlength (keys))) ” 
  &&  “ (0 <= un) ” 
  &&  “ (un <= 200000) ” 
  &&  “ (increasing keys ) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (RightBuildState values i keys right_data ) ” 
  &&  “ (left_data = (repeat_Z (0) (un))) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 right_data 0)) /\ ((Znth j_3 right_data 0) <= i))) ”
  &&  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.full right un right_data )
.

Definition solver_partial_solve_wit_17 := solver_partial_solve_wit_17_pure -> solver_partial_solve_wit_17_aux.

Definition solver_partial_solve_wit_18 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (index: Z) (PreH1 : (a <> 0)) (PreH2 : (vals <> 0)) (PreH3 : (left <> 0)) (PreH4 : (right <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 200000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : (1 <= un)) (PreH11 : (un <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((Zlength (sorted)) = n_pre)) (PreH15 : ((Zlength (keys)) = un)) (PreH16 : ((Zlength (tail)) = (n_pre - un ))) (PreH17 : ((Zlength (left_data)) = un)) (PreH18 : ((Zlength (right_data)) = un)) (PreH19 : (Permutation values sorted )) (PreH20 : (increasing sorted )) (PreH21 : (UniqueKeys sorted keys )) (PreH22 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH23 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH24 : (0 <= index)) (PreH25 : (index < un)) (PreH26 : (KeyAt keys (Znth i values 0) index )) (PreH27 : (RightBuildState values i keys right_data )) (PreH28 : (left_data = (repeat_Z (0) (un)))) (PreH29 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 right_data 0)) /\ ((Znth j_3 right_data 0) <= i)))) ,
  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.full right un right_data )
|--
  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= index) ” 
  &&  “ (index < un) ” 
  &&  “ (KeyAt keys (Znth i values 0) index ) ” 
  &&  “ (RightBuildState values i keys right_data ) ” 
  &&  “ (left_data = (repeat_Z (0) (un))) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 right_data 0)) /\ ((Znth j_3 right_data 0) <= i))) ”
  &&  (((right + (index * sizeof(INT64)))) # Int64  |-> (Znth index right_data 0))
  **  (Int64Array.missing_i right index 0 un right_data )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
.

Definition solver_partial_solve_wit_19 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (index: Z) (PreH1 : (a <> 0)) (PreH2 : (vals <> 0)) (PreH3 : (left <> 0)) (PreH4 : (right <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 200000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : (1 <= un)) (PreH11 : (un <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((Zlength (sorted)) = n_pre)) (PreH15 : ((Zlength (keys)) = un)) (PreH16 : ((Zlength (tail)) = (n_pre - un ))) (PreH17 : ((Zlength (left_data)) = un)) (PreH18 : ((Zlength (right_data)) = un)) (PreH19 : (Permutation values sorted )) (PreH20 : (increasing sorted )) (PreH21 : (UniqueKeys sorted keys )) (PreH22 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH23 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH24 : (0 <= index)) (PreH25 : (index < un)) (PreH26 : (KeyAt keys (Znth i values 0) index )) (PreH27 : (RightBuildState values i keys right_data )) (PreH28 : (left_data = (repeat_Z (0) (un)))) (PreH29 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 right_data 0)) /\ ((Znth j_3 right_data 0) <= i)))) ,
  (Int64Array.full right un right_data )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
|--
  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= index) ” 
  &&  “ (index < un) ” 
  &&  “ (KeyAt keys (Znth i values 0) index ) ” 
  &&  “ (RightBuildState values i keys right_data ) ” 
  &&  “ (left_data = (repeat_Z (0) (un))) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 right_data 0)) /\ ((Znth j_3 right_data 0) <= i))) ”
  &&  (((right + (index * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i right index 0 un right_data )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
.

Definition solver_partial_solve_wit_20 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (ans: Z) (i: Z) (right_data: (@list Z)) (left_data: (@list Z)) (tail: (@list Z)) (keys: (@list Z)) (sorted: (@list Z)) (un: Z) (right: Z) (left: Z) (vals: Z) (a: Z) (PreH1 : (i < n_pre)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (left <> 0)) (PreH5 : (right <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (1 <= un)) (PreH12 : (un <= n_pre)) (PreH13 : ((Zlength (sorted)) = n_pre)) (PreH14 : ((Zlength (keys)) = un)) (PreH15 : ((Zlength (tail)) = (n_pre - un ))) (PreH16 : ((Zlength (left_data)) = un)) (PreH17 : ((Zlength (right_data)) = un)) (PreH18 : (Permutation values sorted )) (PreH19 : (increasing sorted )) (PreH20 : (UniqueKeys sorted keys )) (PreH21 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH22 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH23 : (0 <= i)) (PreH24 : (i <= n_pre)) (PreH25 : (0 <= ans)) (PreH26 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH27 : (CountingState k_pre values i keys left_data right_data ans )) (PreH28 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH29 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.full right un right_data )
|--
  “ (i < n_pre) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= ((n_pre * n_pre ) * n_pre )) ” 
  &&  “ (CountingState k_pre values i keys left_data right_data ans ) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i )))) ”
  &&  (((a + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.missing_i a i 0 n_pre values )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.full right un right_data )
.

Definition solver_partial_solve_wit_21_pure := 
(
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (ans: Z) (i: Z) (right_data: (@list Z)) (left_data: (@list Z)) (tail: (@list Z)) (keys: (@list Z)) (sorted: (@list Z)) (un: Z) (right: Z) (left: Z) (vals: Z) (a: Z) (PreH1 : (i < n_pre)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (left <> 0)) (PreH5 : (right <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (1 <= un)) (PreH12 : (un <= n_pre)) (PreH13 : ((Zlength (sorted)) = n_pre)) (PreH14 : ((Zlength (keys)) = un)) (PreH15 : ((Zlength (tail)) = (n_pre - un ))) (PreH16 : ((Zlength (left_data)) = un)) (PreH17 : ((Zlength (right_data)) = un)) (PreH18 : (Permutation values sorted )) (PreH19 : (increasing sorted )) (PreH20 : (UniqueKeys sorted keys )) (PreH21 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH22 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH23 : (0 <= i)) (PreH24 : (i <= n_pre)) (PreH25 : (0 <= ans)) (PreH26 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH27 : (CountingState k_pre values i keys left_data right_data ans )) (PreH28 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH29 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full a n_pre values )
  **  ((( &( "ix" ) )) # Int  |->_)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.full right un right_data )
|--
  “ (un = (Zlength (keys))) ” 
  &&  “ (0 <= un) ” 
  &&  “ (un <= 200000) ” 
  &&  “ (increasing keys ) ”
) \/
(
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (ans: Z) (i: Z) (right_data: (@list Z)) (left_data: (@list Z)) (tail: (@list Z)) (keys: (@list Z)) (sorted: (@list Z)) (un: Z) (right: Z) (left: Z) (vals: Z) (a: Z) (PreH1 : (ans <= INT64_MAX)) (PreH2 : (k_pre <= INT64_MAX)) (PreH3 : (ans >= INT64_MIN)) (PreH4 : (k_pre >= INT64_MIN)) (PreH5 : (i <= INT_MAX)) (PreH6 : (un <= INT_MAX)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (i >= INT_MIN)) (PreH9 : (un >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (a <> 0)) (PreH13 : (vals <> 0)) (PreH14 : (left <> 0)) (PreH15 : (right <> 0)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (1 <= k_pre)) (PreH18 : (k_pre <= 200000)) (PreH19 : (1 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (1 <= un)) (PreH22 : (un <= n_pre)) (PreH23 : ((Zlength (sorted)) = n_pre)) (PreH24 : ((Zlength (keys)) = un)) (PreH25 : ((Zlength (tail)) = (n_pre - un ))) (PreH26 : ((Zlength (left_data)) = un)) (PreH27 : ((Zlength (right_data)) = un)) (PreH28 : (Permutation values sorted )) (PreH29 : (increasing sorted )) (PreH30 : (UniqueKeys sorted keys )) (PreH31 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH32 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH33 : (0 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (0 <= ans)) (PreH36 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH37 : (CountingState k_pre values i keys left_data right_data ans )) (PreH38 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH39 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full a n_pre values )
  **  ((( &( "ix" ) )) # Int  |->_)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.full right un right_data )
|--
  “ (increasing keys ) ”
).

Definition solver_partial_solve_wit_21_pure_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (ans: Z) (i: Z) (right_data: (@list Z)) (left_data: (@list Z)) (tail: (@list Z)) (keys: (@list Z)) (sorted: (@list Z)) (un: Z) (right: Z) (left: Z) (vals: Z) (a: Z) (PreH1 : (ans <= INT64_MAX)) (PreH2 : (k_pre <= INT64_MAX)) (PreH3 : (ans >= INT64_MIN)) (PreH4 : (k_pre >= INT64_MIN)) (PreH5 : (i <= INT_MAX)) (PreH6 : (un <= INT_MAX)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (i >= INT_MIN)) (PreH9 : (un >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (a <> 0)) (PreH13 : (vals <> 0)) (PreH14 : (left <> 0)) (PreH15 : (right <> 0)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (1 <= k_pre)) (PreH18 : (k_pre <= 200000)) (PreH19 : (1 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (1 <= un)) (PreH22 : (un <= n_pre)) (PreH23 : ((Zlength (sorted)) = n_pre)) (PreH24 : ((Zlength (keys)) = un)) (PreH25 : ((Zlength (tail)) = (n_pre - un ))) (PreH26 : ((Zlength (left_data)) = un)) (PreH27 : ((Zlength (right_data)) = un)) (PreH28 : (Permutation values sorted )) (PreH29 : (increasing sorted )) (PreH30 : (UniqueKeys sorted keys )) (PreH31 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH32 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH33 : (0 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (0 <= ans)) (PreH36 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH37 : (CountingState k_pre values i keys left_data right_data ans )) (PreH38 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH39 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full a n_pre values )
  **  ((( &( "ix" ) )) # Int  |->_)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.full right un right_data )
|--
  “ (increasing keys ) ”
.

Definition solver_partial_solve_wit_21_aux := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (ans: Z) (i: Z) (right_data: (@list Z)) (left_data: (@list Z)) (tail: (@list Z)) (keys: (@list Z)) (sorted: (@list Z)) (un: Z) (right: Z) (left: Z) (vals: Z) (a: Z) (PreH1 : (i < n_pre)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (left <> 0)) (PreH5 : (right <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (1 <= un)) (PreH12 : (un <= n_pre)) (PreH13 : ((Zlength (sorted)) = n_pre)) (PreH14 : ((Zlength (keys)) = un)) (PreH15 : ((Zlength (tail)) = (n_pre - un ))) (PreH16 : ((Zlength (left_data)) = un)) (PreH17 : ((Zlength (right_data)) = un)) (PreH18 : (Permutation values sorted )) (PreH19 : (increasing sorted )) (PreH20 : (UniqueKeys sorted keys )) (PreH21 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH22 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH23 : (0 <= i)) (PreH24 : (i <= n_pre)) (PreH25 : (0 <= ans)) (PreH26 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH27 : (CountingState k_pre values i keys left_data right_data ans )) (PreH28 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH29 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full a n_pre values )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.full right un right_data )
|--
  “ (un = (Zlength (keys))) ” 
  &&  “ (0 <= un) ” 
  &&  “ (un <= 200000) ” 
  &&  “ (increasing keys ) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= ((n_pre * n_pre ) * n_pre )) ” 
  &&  “ (CountingState k_pre values i keys left_data right_data ans ) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i )))) ”
  &&  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.full right un right_data )
.

Definition solver_partial_solve_wit_21 := solver_partial_solve_wit_21_pure -> solver_partial_solve_wit_21_aux.

Definition solver_partial_solve_wit_22 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (PreH1 : (a <> 0)) (PreH2 : (vals <> 0)) (PreH3 : (left <> 0)) (PreH4 : (right <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 200000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : (1 <= un)) (PreH11 : (un <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH16 : ((Zlength (sorted)) = n_pre)) (PreH17 : ((Zlength (keys)) = un)) (PreH18 : ((Zlength (tail)) = (n_pre - un ))) (PreH19 : ((Zlength (left_data)) = un)) (PreH20 : ((Zlength (right_data)) = un)) (PreH21 : (Permutation values sorted )) (PreH22 : (increasing sorted )) (PreH23 : (UniqueKeys sorted keys )) (PreH24 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH25 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH26 : (0 <= ix)) (PreH27 : (ix < un)) (PreH28 : (KeyAt keys (Znth i values 0) ix )) (PreH29 : (CountingState k_pre values i keys left_data right_data ans )) (PreH30 : (1 <= (Znth ix right_data 0))) (PreH31 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH32 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH33 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.full right un right_data )
|--
  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= ((n_pre * n_pre ) * n_pre )) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < un) ” 
  &&  “ (KeyAt keys (Znth i values 0) ix ) ” 
  &&  “ (CountingState k_pre values i keys left_data right_data ans ) ” 
  &&  “ (1 <= (Znth ix right_data 0)) ” 
  &&  “ ((Znth ix right_data 0) <= (n_pre - i )) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i )))) ”
  &&  (((right + (ix * sizeof(INT64)))) # Int64  |-> (Znth ix right_data 0))
  **  (Int64Array.missing_i right ix 0 un right_data )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
.

Definition solver_partial_solve_wit_23 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (PreH1 : (a <> 0)) (PreH2 : (vals <> 0)) (PreH3 : (left <> 0)) (PreH4 : (right <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 200000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : (1 <= un)) (PreH11 : (un <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH16 : ((Zlength (sorted)) = n_pre)) (PreH17 : ((Zlength (keys)) = un)) (PreH18 : ((Zlength (tail)) = (n_pre - un ))) (PreH19 : ((Zlength (left_data)) = un)) (PreH20 : ((Zlength (right_data)) = un)) (PreH21 : (Permutation values sorted )) (PreH22 : (increasing sorted )) (PreH23 : (UniqueKeys sorted keys )) (PreH24 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH25 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH26 : (0 <= ix)) (PreH27 : (ix < un)) (PreH28 : (KeyAt keys (Znth i values 0) ix )) (PreH29 : (CountingState k_pre values i keys left_data right_data ans )) (PreH30 : (1 <= (Znth ix right_data 0))) (PreH31 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH32 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH33 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full right un right_data )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
|--
  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= ((n_pre * n_pre ) * n_pre )) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < un) ” 
  &&  “ (KeyAt keys (Znth i values 0) ix ) ” 
  &&  “ (CountingState k_pre values i keys left_data right_data ans ) ” 
  &&  “ (1 <= (Znth ix right_data 0)) ” 
  &&  “ ((Znth ix right_data 0) <= (n_pre - i )) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i )))) ”
  &&  (((right + (ix * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i right ix 0 un right_data )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
.

Definition solver_partial_solve_wit_24 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (PreH1 : (a <> 0)) (PreH2 : (vals <> 0)) (PreH3 : (left <> 0)) (PreH4 : (right <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 200000)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : (1 <= un)) (PreH11 : (un <= n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH16 : ((Zlength (sorted)) = n_pre)) (PreH17 : ((Zlength (keys)) = un)) (PreH18 : ((Zlength (tail)) = (n_pre - un ))) (PreH19 : ((Zlength (left_data)) = un)) (PreH20 : ((Zlength (right_data)) = un)) (PreH21 : (Permutation values sorted )) (PreH22 : (increasing sorted )) (PreH23 : (UniqueKeys sorted keys )) (PreH24 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH25 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH26 : (0 <= ix)) (PreH27 : (ix < un)) (PreH28 : (KeyAt keys (Znth i values 0) ix )) (PreH29 : (CountingState k_pre values i keys left_data right_data ans )) (PreH30 : (1 <= (Znth ix right_data 0))) (PreH31 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH32 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH33 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
|--
  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= ((n_pre * n_pre ) * n_pre )) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < un) ” 
  &&  “ (KeyAt keys (Znth i values 0) ix ) ” 
  &&  “ (CountingState k_pre values i keys left_data right_data ans ) ” 
  &&  “ (1 <= (Znth ix right_data 0)) ” 
  &&  “ ((Znth ix right_data 0) <= (n_pre - i )) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i )))) ”
  &&  (((a + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.missing_i a i 0 n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
.

Definition solver_partial_solve_wit_25 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (PreH1 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (left <> 0)) (PreH5 : (right <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (1 <= un)) (PreH12 : (un <= n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= ans)) (PreH16 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH17 : ((Zlength (sorted)) = n_pre)) (PreH18 : ((Zlength (keys)) = un)) (PreH19 : ((Zlength (tail)) = (n_pre - un ))) (PreH20 : ((Zlength (left_data)) = un)) (PreH21 : ((Zlength (right_data)) = un)) (PreH22 : (Permutation values sorted )) (PreH23 : (increasing sorted )) (PreH24 : (UniqueKeys sorted keys )) (PreH25 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH26 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH27 : (0 <= ix)) (PreH28 : (ix < un)) (PreH29 : (KeyAt keys (Znth i values 0) ix )) (PreH30 : (CountingState k_pre values i keys left_data right_data ans )) (PreH31 : (1 <= (Znth ix right_data 0))) (PreH32 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH33 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH34 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
|--
  “ (((Znth i values 0) % ( k_pre ) ) = 0) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= ((n_pre * n_pre ) * n_pre )) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < un) ” 
  &&  “ (KeyAt keys (Znth i values 0) ix ) ” 
  &&  “ (CountingState k_pre values i keys left_data right_data ans ) ” 
  &&  “ (1 <= (Znth ix right_data 0)) ” 
  &&  “ ((Znth ix right_data 0) <= (n_pre - i )) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i )))) ”
  &&  (((a + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.missing_i a i 0 n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
.

Definition solver_partial_solve_wit_26 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (PreH1 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (left <> 0)) (PreH5 : (right <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (1 <= un)) (PreH12 : (un <= n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= ans)) (PreH16 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH17 : ((Zlength (sorted)) = n_pre)) (PreH18 : ((Zlength (keys)) = un)) (PreH19 : ((Zlength (tail)) = (n_pre - un ))) (PreH20 : ((Zlength (left_data)) = un)) (PreH21 : ((Zlength (right_data)) = un)) (PreH22 : (Permutation values sorted )) (PreH23 : (increasing sorted )) (PreH24 : (UniqueKeys sorted keys )) (PreH25 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH26 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH27 : (0 <= ix)) (PreH28 : (ix < un)) (PreH29 : (KeyAt keys (Znth i values 0) ix )) (PreH30 : (CountingState k_pre values i keys left_data right_data ans )) (PreH31 : (1 <= (Znth ix right_data 0))) (PreH32 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH33 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH34 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
|--
  “ (((Znth i values 0) % ( k_pre ) ) = 0) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= ((n_pre * n_pre ) * n_pre )) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < un) ” 
  &&  “ (KeyAt keys (Znth i values 0) ix ) ” 
  &&  “ (CountingState k_pre values i keys left_data right_data ans ) ” 
  &&  “ (1 <= (Znth ix right_data 0)) ” 
  &&  “ ((Znth ix right_data 0) <= (n_pre - i )) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i )))) ”
  &&  (((a + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.missing_i a i 0 n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
.

Definition solver_partial_solve_wit_27_pure := 
(
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (PreH1 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (left <> 0)) (PreH5 : (right <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (1 <= un)) (PreH12 : (un <= n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= ans)) (PreH16 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH17 : ((Zlength (sorted)) = n_pre)) (PreH18 : ((Zlength (keys)) = un)) (PreH19 : ((Zlength (tail)) = (n_pre - un ))) (PreH20 : ((Zlength (left_data)) = un)) (PreH21 : ((Zlength (right_data)) = un)) (PreH22 : (Permutation values sorted )) (PreH23 : (increasing sorted )) (PreH24 : (UniqueKeys sorted keys )) (PreH25 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH26 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH27 : (0 <= ix)) (PreH28 : (ix < un)) (PreH29 : (KeyAt keys (Znth i values 0) ix )) (PreH30 : (CountingState k_pre values i keys left_data right_data ans )) (PreH31 : (1 <= (Znth ix right_data 0))) (PreH32 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH33 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH34 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  ((( &( "li" ) )) # Int  |->_)
  **  (Int64Array.full a n_pre values )
  **  ((( &( "hi" ) )) # Int64  |-> ((Znth i values 0) * k_pre ))
  **  ((( &( "lo" ) )) # Int64  |-> ((Znth i values 0) ÷ k_pre ))
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  ((( &( "ix" ) )) # Int  |-> ix)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
|--
  “ (un = (Zlength (keys))) ” 
  &&  “ (0 <= un) ” 
  &&  “ (un <= 200000) ” 
  &&  “ (increasing keys ) ”
) \/
(
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (PreH1 : (ans <= INT64_MAX)) (PreH2 : (k_pre <= INT64_MAX)) (PreH3 : (((Znth i values 0) ÷ k_pre ) <= INT64_MAX)) (PreH4 : (((Znth i values 0) * k_pre ) <= INT64_MAX)) (PreH5 : (ans >= INT64_MIN)) (PreH6 : (k_pre >= INT64_MIN)) (PreH7 : (((Znth i values 0) ÷ k_pre ) >= INT64_MIN)) (PreH8 : (((Znth i values 0) * k_pre ) >= INT64_MIN)) (PreH9 : (ix <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (un <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (ix >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (un >= INT_MIN)) (PreH16 : (n_pre >= INT_MIN)) (PreH17 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH18 : (a <> 0)) (PreH19 : (vals <> 0)) (PreH20 : (left <> 0)) (PreH21 : (right <> 0)) (PreH22 : (n_pre = (Zlength (values)))) (PreH23 : (1 <= k_pre)) (PreH24 : (k_pre <= 200000)) (PreH25 : (1 <= n_pre)) (PreH26 : (n_pre <= 200000)) (PreH27 : (1 <= un)) (PreH28 : (un <= n_pre)) (PreH29 : (0 <= i)) (PreH30 : (i < n_pre)) (PreH31 : (0 <= ans)) (PreH32 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH33 : ((Zlength (sorted)) = n_pre)) (PreH34 : ((Zlength (keys)) = un)) (PreH35 : ((Zlength (tail)) = (n_pre - un ))) (PreH36 : ((Zlength (left_data)) = un)) (PreH37 : ((Zlength (right_data)) = un)) (PreH38 : (Permutation values sorted )) (PreH39 : (increasing sorted )) (PreH40 : (UniqueKeys sorted keys )) (PreH41 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH42 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH43 : (0 <= ix)) (PreH44 : (ix < un)) (PreH45 : (KeyAt keys (Znth i values 0) ix )) (PreH46 : (CountingState k_pre values i keys left_data right_data ans )) (PreH47 : (1 <= (Znth ix right_data 0))) (PreH48 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH49 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH50 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  ((( &( "li" ) )) # Int  |->_)
  **  (Int64Array.full a n_pre values )
  **  ((( &( "hi" ) )) # Int64  |-> ((Znth i values 0) * k_pre ))
  **  ((( &( "lo" ) )) # Int64  |-> ((Znth i values 0) ÷ k_pre ))
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  ((( &( "ix" ) )) # Int  |-> ix)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
|--
  “ (increasing keys ) ”
).

Definition solver_partial_solve_wit_27_pure_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (PreH1 : (ans <= INT64_MAX)) (PreH2 : (k_pre <= INT64_MAX)) (PreH3 : (((Znth i values 0) ÷ k_pre ) <= INT64_MAX)) (PreH4 : (((Znth i values 0) * k_pre ) <= INT64_MAX)) (PreH5 : (ans >= INT64_MIN)) (PreH6 : (k_pre >= INT64_MIN)) (PreH7 : (((Znth i values 0) ÷ k_pre ) >= INT64_MIN)) (PreH8 : (((Znth i values 0) * k_pre ) >= INT64_MIN)) (PreH9 : (ix <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (un <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (ix >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (un >= INT_MIN)) (PreH16 : (n_pre >= INT_MIN)) (PreH17 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH18 : (a <> 0)) (PreH19 : (vals <> 0)) (PreH20 : (left <> 0)) (PreH21 : (right <> 0)) (PreH22 : (n_pre = (Zlength (values)))) (PreH23 : (1 <= k_pre)) (PreH24 : (k_pre <= 200000)) (PreH25 : (1 <= n_pre)) (PreH26 : (n_pre <= 200000)) (PreH27 : (1 <= un)) (PreH28 : (un <= n_pre)) (PreH29 : (0 <= i)) (PreH30 : (i < n_pre)) (PreH31 : (0 <= ans)) (PreH32 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH33 : ((Zlength (sorted)) = n_pre)) (PreH34 : ((Zlength (keys)) = un)) (PreH35 : ((Zlength (tail)) = (n_pre - un ))) (PreH36 : ((Zlength (left_data)) = un)) (PreH37 : ((Zlength (right_data)) = un)) (PreH38 : (Permutation values sorted )) (PreH39 : (increasing sorted )) (PreH40 : (UniqueKeys sorted keys )) (PreH41 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH42 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH43 : (0 <= ix)) (PreH44 : (ix < un)) (PreH45 : (KeyAt keys (Znth i values 0) ix )) (PreH46 : (CountingState k_pre values i keys left_data right_data ans )) (PreH47 : (1 <= (Znth ix right_data 0))) (PreH48 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH49 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH50 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  ((( &( "li" ) )) # Int  |->_)
  **  (Int64Array.full a n_pre values )
  **  ((( &( "hi" ) )) # Int64  |-> ((Znth i values 0) * k_pre ))
  **  ((( &( "lo" ) )) # Int64  |-> ((Znth i values 0) ÷ k_pre ))
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  ((( &( "ix" ) )) # Int  |-> ix)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
|--
  “ (increasing keys ) ”
.

Definition solver_partial_solve_wit_27_aux := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (PreH1 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (left <> 0)) (PreH5 : (right <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (1 <= un)) (PreH12 : (un <= n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= ans)) (PreH16 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH17 : ((Zlength (sorted)) = n_pre)) (PreH18 : ((Zlength (keys)) = un)) (PreH19 : ((Zlength (tail)) = (n_pre - un ))) (PreH20 : ((Zlength (left_data)) = un)) (PreH21 : ((Zlength (right_data)) = un)) (PreH22 : (Permutation values sorted )) (PreH23 : (increasing sorted )) (PreH24 : (UniqueKeys sorted keys )) (PreH25 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH26 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH27 : (0 <= ix)) (PreH28 : (ix < un)) (PreH29 : (KeyAt keys (Znth i values 0) ix )) (PreH30 : (CountingState k_pre values i keys left_data right_data ans )) (PreH31 : (1 <= (Znth ix right_data 0))) (PreH32 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH33 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH34 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
|--
  “ (un = (Zlength (keys))) ” 
  &&  “ (0 <= un) ” 
  &&  “ (un <= 200000) ” 
  &&  “ (increasing keys ) ” 
  &&  “ (((Znth i values 0) % ( k_pre ) ) = 0) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= ((n_pre * n_pre ) * n_pre )) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < un) ” 
  &&  “ (KeyAt keys (Znth i values 0) ix ) ” 
  &&  “ (CountingState k_pre values i keys left_data right_data ans ) ” 
  &&  “ (1 <= (Znth ix right_data 0)) ” 
  &&  “ ((Znth ix right_data 0) <= (n_pre - i )) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i )))) ”
  &&  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
.

Definition solver_partial_solve_wit_27 := solver_partial_solve_wit_27_pure -> solver_partial_solve_wit_27_aux.

Definition solver_partial_solve_wit_28_pure := 
(
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= un)) (PreH3 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH4 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH5 : (a <> 0)) (PreH6 : (vals <> 0)) (PreH7 : (left <> 0)) (PreH8 : (right <> 0)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (1 <= k_pre)) (PreH11 : (k_pre <= 200000)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (1 <= un)) (PreH15 : (un <= n_pre)) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (0 <= ans)) (PreH19 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH20 : ((Zlength (sorted)) = n_pre)) (PreH21 : ((Zlength (keys)) = un)) (PreH22 : ((Zlength (tail)) = (n_pre - un ))) (PreH23 : ((Zlength (left_data)) = un)) (PreH24 : ((Zlength (right_data)) = un)) (PreH25 : (Permutation values sorted )) (PreH26 : (increasing sorted )) (PreH27 : (UniqueKeys sorted keys )) (PreH28 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH29 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH30 : (0 <= ix)) (PreH31 : (ix < un)) (PreH32 : (KeyAt keys (Znth i values 0) ix )) (PreH33 : (CountingState k_pre values i keys left_data right_data ans )) (PreH34 : (1 <= (Znth ix right_data 0))) (PreH35 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH36 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH37 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  ((( &( "ri" ) )) # Int  |->_)
  **  (Int64Array.seg vals 0 un keys )
  **  ((( &( "li" ) )) # Int  |-> retval)
  **  (Int64Array.full a n_pre values )
  **  ((( &( "hi" ) )) # Int64  |-> ((Znth i values 0) * k_pre ))
  **  ((( &( "lo" ) )) # Int64  |-> ((Znth i values 0) ÷ k_pre ))
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  ((( &( "ix" ) )) # Int  |-> ix)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
|--
  “ (un = (Zlength (keys))) ” 
  &&  “ (0 <= un) ” 
  &&  “ (un <= 200000) ” 
  &&  “ (increasing keys ) ”
) \/
(
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (PreH1 : (ans <= INT64_MAX)) (PreH2 : (k_pre <= INT64_MAX)) (PreH3 : (((Znth i values 0) ÷ k_pre ) <= INT64_MAX)) (PreH4 : (((Znth i values 0) * k_pre ) <= INT64_MAX)) (PreH5 : (ans >= INT64_MIN)) (PreH6 : (k_pre >= INT64_MIN)) (PreH7 : (((Znth i values 0) ÷ k_pre ) >= INT64_MIN)) (PreH8 : (((Znth i values 0) * k_pre ) >= INT64_MIN)) (PreH9 : (ix <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (un <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (retval <= INT_MAX)) (PreH14 : (ix >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (un >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : (retval >= INT_MIN)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= un)) (PreH21 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH22 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH23 : (a <> 0)) (PreH24 : (vals <> 0)) (PreH25 : (left <> 0)) (PreH26 : (right <> 0)) (PreH27 : (n_pre = (Zlength (values)))) (PreH28 : (1 <= k_pre)) (PreH29 : (k_pre <= 200000)) (PreH30 : (1 <= n_pre)) (PreH31 : (n_pre <= 200000)) (PreH32 : (1 <= un)) (PreH33 : (un <= n_pre)) (PreH34 : (0 <= i)) (PreH35 : (i < n_pre)) (PreH36 : (0 <= ans)) (PreH37 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH38 : ((Zlength (sorted)) = n_pre)) (PreH39 : ((Zlength (keys)) = un)) (PreH40 : ((Zlength (tail)) = (n_pre - un ))) (PreH41 : ((Zlength (left_data)) = un)) (PreH42 : ((Zlength (right_data)) = un)) (PreH43 : (Permutation values sorted )) (PreH44 : (increasing sorted )) (PreH45 : (UniqueKeys sorted keys )) (PreH46 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH47 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH48 : (0 <= ix)) (PreH49 : (ix < un)) (PreH50 : (KeyAt keys (Znth i values 0) ix )) (PreH51 : (CountingState k_pre values i keys left_data right_data ans )) (PreH52 : (1 <= (Znth ix right_data 0))) (PreH53 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH54 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH55 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  ((( &( "ri" ) )) # Int  |->_)
  **  (Int64Array.seg vals 0 un keys )
  **  ((( &( "li" ) )) # Int  |-> retval)
  **  (Int64Array.full a n_pre values )
  **  ((( &( "hi" ) )) # Int64  |-> ((Znth i values 0) * k_pre ))
  **  ((( &( "lo" ) )) # Int64  |-> ((Znth i values 0) ÷ k_pre ))
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  ((( &( "ix" ) )) # Int  |-> ix)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
|--
  “ (increasing keys ) ”
).

Definition solver_partial_solve_wit_28_pure_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (PreH1 : (ans <= INT64_MAX)) (PreH2 : (k_pre <= INT64_MAX)) (PreH3 : (((Znth i values 0) ÷ k_pre ) <= INT64_MAX)) (PreH4 : (((Znth i values 0) * k_pre ) <= INT64_MAX)) (PreH5 : (ans >= INT64_MIN)) (PreH6 : (k_pre >= INT64_MIN)) (PreH7 : (((Znth i values 0) ÷ k_pre ) >= INT64_MIN)) (PreH8 : (((Znth i values 0) * k_pre ) >= INT64_MIN)) (PreH9 : (ix <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (un <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (retval <= INT_MAX)) (PreH14 : (ix >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (un >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : (retval >= INT_MIN)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= un)) (PreH21 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH22 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH23 : (a <> 0)) (PreH24 : (vals <> 0)) (PreH25 : (left <> 0)) (PreH26 : (right <> 0)) (PreH27 : (n_pre = (Zlength (values)))) (PreH28 : (1 <= k_pre)) (PreH29 : (k_pre <= 200000)) (PreH30 : (1 <= n_pre)) (PreH31 : (n_pre <= 200000)) (PreH32 : (1 <= un)) (PreH33 : (un <= n_pre)) (PreH34 : (0 <= i)) (PreH35 : (i < n_pre)) (PreH36 : (0 <= ans)) (PreH37 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH38 : ((Zlength (sorted)) = n_pre)) (PreH39 : ((Zlength (keys)) = un)) (PreH40 : ((Zlength (tail)) = (n_pre - un ))) (PreH41 : ((Zlength (left_data)) = un)) (PreH42 : ((Zlength (right_data)) = un)) (PreH43 : (Permutation values sorted )) (PreH44 : (increasing sorted )) (PreH45 : (UniqueKeys sorted keys )) (PreH46 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH47 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH48 : (0 <= ix)) (PreH49 : (ix < un)) (PreH50 : (KeyAt keys (Znth i values 0) ix )) (PreH51 : (CountingState k_pre values i keys left_data right_data ans )) (PreH52 : (1 <= (Znth ix right_data 0))) (PreH53 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH54 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH55 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  ((( &( "ri" ) )) # Int  |->_)
  **  (Int64Array.seg vals 0 un keys )
  **  ((( &( "li" ) )) # Int  |-> retval)
  **  (Int64Array.full a n_pre values )
  **  ((( &( "hi" ) )) # Int64  |-> ((Znth i values 0) * k_pre ))
  **  ((( &( "lo" ) )) # Int64  |-> ((Znth i values 0) ÷ k_pre ))
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "vals" ) )) # Ptr  |-> vals)
  **  ((( &( "left" ) )) # Ptr  |-> left)
  **  ((( &( "right" ) )) # Ptr  |-> right)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  ((( &( "ix" ) )) # Int  |-> ix)
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
|--
  “ (increasing keys ) ”
.

Definition solver_partial_solve_wit_28_aux := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= un)) (PreH3 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH4 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH5 : (a <> 0)) (PreH6 : (vals <> 0)) (PreH7 : (left <> 0)) (PreH8 : (right <> 0)) (PreH9 : (n_pre = (Zlength (values)))) (PreH10 : (1 <= k_pre)) (PreH11 : (k_pre <= 200000)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 200000)) (PreH14 : (1 <= un)) (PreH15 : (un <= n_pre)) (PreH16 : (0 <= i)) (PreH17 : (i < n_pre)) (PreH18 : (0 <= ans)) (PreH19 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH20 : ((Zlength (sorted)) = n_pre)) (PreH21 : ((Zlength (keys)) = un)) (PreH22 : ((Zlength (tail)) = (n_pre - un ))) (PreH23 : ((Zlength (left_data)) = un)) (PreH24 : ((Zlength (right_data)) = un)) (PreH25 : (Permutation values sorted )) (PreH26 : (increasing sorted )) (PreH27 : (UniqueKeys sorted keys )) (PreH28 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH29 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH30 : (0 <= ix)) (PreH31 : (ix < un)) (PreH32 : (KeyAt keys (Znth i values 0) ix )) (PreH33 : (CountingState k_pre values i keys left_data right_data ans )) (PreH34 : (1 <= (Znth ix right_data 0))) (PreH35 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH36 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH37 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
|--
  “ (un = (Zlength (keys))) ” 
  &&  “ (0 <= un) ” 
  &&  “ (un <= 200000) ” 
  &&  “ (increasing keys ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= un) ” 
  &&  “ (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval ) ” 
  &&  “ (((Znth i values 0) % ( k_pre ) ) = 0) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= ((n_pre * n_pre ) * n_pre )) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < un) ” 
  &&  “ (KeyAt keys (Znth i values 0) ix ) ” 
  &&  “ (CountingState k_pre values i keys left_data right_data ans ) ” 
  &&  “ (1 <= (Znth ix right_data 0)) ” 
  &&  “ ((Znth ix right_data 0) <= (n_pre - i )) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i )))) ”
  &&  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
.

Definition solver_partial_solve_wit_28 := solver_partial_solve_wit_28_pure -> solver_partial_solve_wit_28_aux.

Definition solver_partial_solve_wit_29 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval < un)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= un)) (PreH4 : (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 )) (PreH5 : (0 <= retval)) (PreH6 : (retval <= un)) (PreH7 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH8 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH9 : (a <> 0)) (PreH10 : (vals <> 0)) (PreH11 : (left <> 0)) (PreH12 : (right <> 0)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : (1 <= k_pre)) (PreH15 : (k_pre <= 200000)) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 200000)) (PreH18 : (1 <= un)) (PreH19 : (un <= n_pre)) (PreH20 : (0 <= i)) (PreH21 : (i < n_pre)) (PreH22 : (0 <= ans)) (PreH23 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH24 : ((Zlength (sorted)) = n_pre)) (PreH25 : ((Zlength (keys)) = un)) (PreH26 : ((Zlength (tail)) = (n_pre - un ))) (PreH27 : ((Zlength (left_data)) = un)) (PreH28 : ((Zlength (right_data)) = un)) (PreH29 : (Permutation values sorted )) (PreH30 : (increasing sorted )) (PreH31 : (UniqueKeys sorted keys )) (PreH32 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH33 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH34 : (0 <= ix)) (PreH35 : (ix < un)) (PreH36 : (KeyAt keys (Znth i values 0) ix )) (PreH37 : (CountingState k_pre values i keys left_data right_data ans )) (PreH38 : (1 <= (Znth ix right_data 0))) (PreH39 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH40 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH41 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
|--
  “ (retval < un) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= un) ” 
  &&  “ (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= un) ” 
  &&  “ (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval ) ” 
  &&  “ (((Znth i values 0) % ( k_pre ) ) = 0) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= ((n_pre * n_pre ) * n_pre )) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < un) ” 
  &&  “ (KeyAt keys (Znth i values 0) ix ) ” 
  &&  “ (CountingState k_pre values i keys left_data right_data ans ) ” 
  &&  “ (1 <= (Znth ix right_data 0)) ” 
  &&  “ ((Znth ix right_data 0) <= (n_pre - i )) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i )))) ”
  &&  (((vals + (retval * sizeof(INT64)))) # Int64  |-> (Znth (retval - 0 ) keys 0))
  **  (Int64Array.missing_i vals retval 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
.

Definition solver_partial_solve_wit_30 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 < un)) (PreH2 : ((Znth (retval - 0 ) keys 0) = ((Znth i values 0) ÷ k_pre ))) (PreH3 : (retval < un)) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= un)) (PreH6 : (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 )) (PreH7 : (0 <= retval)) (PreH8 : (retval <= un)) (PreH9 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH10 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH11 : (a <> 0)) (PreH12 : (vals <> 0)) (PreH13 : (left <> 0)) (PreH14 : (right <> 0)) (PreH15 : (n_pre = (Zlength (values)))) (PreH16 : (1 <= k_pre)) (PreH17 : (k_pre <= 200000)) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 200000)) (PreH20 : (1 <= un)) (PreH21 : (un <= n_pre)) (PreH22 : (0 <= i)) (PreH23 : (i < n_pre)) (PreH24 : (0 <= ans)) (PreH25 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH26 : ((Zlength (sorted)) = n_pre)) (PreH27 : ((Zlength (keys)) = un)) (PreH28 : ((Zlength (tail)) = (n_pre - un ))) (PreH29 : ((Zlength (left_data)) = un)) (PreH30 : ((Zlength (right_data)) = un)) (PreH31 : (Permutation values sorted )) (PreH32 : (increasing sorted )) (PreH33 : (UniqueKeys sorted keys )) (PreH34 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH35 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH36 : (0 <= ix)) (PreH37 : (ix < un)) (PreH38 : (KeyAt keys (Znth i values 0) ix )) (PreH39 : (CountingState k_pre values i keys left_data right_data ans )) (PreH40 : (1 <= (Znth ix right_data 0))) (PreH41 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH42 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH43 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
|--
  “ (retval_2 < un) ” 
  &&  “ ((Znth (retval - 0 ) keys 0) = ((Znth i values 0) ÷ k_pre )) ” 
  &&  “ (retval < un) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= un) ” 
  &&  “ (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= un) ” 
  &&  “ (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval ) ” 
  &&  “ (((Znth i values 0) % ( k_pre ) ) = 0) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= ((n_pre * n_pre ) * n_pre )) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < un) ” 
  &&  “ (KeyAt keys (Znth i values 0) ix ) ” 
  &&  “ (CountingState k_pre values i keys left_data right_data ans ) ” 
  &&  “ (1 <= (Znth ix right_data 0)) ” 
  &&  “ ((Znth ix right_data 0) <= (n_pre - i )) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i )))) ”
  &&  (((vals + (retval_2 * sizeof(INT64)))) # Int64  |-> (Znth (retval_2 - 0 ) keys 0))
  **  (Int64Array.missing_i vals retval_2 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
.

Definition solver_partial_solve_wit_31 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth (retval_2 - 0 ) keys 0) = ((Znth i values 0) * k_pre ))) (PreH2 : (retval_2 < un)) (PreH3 : ((Znth (retval - 0 ) keys 0) = ((Znth i values 0) ÷ k_pre ))) (PreH4 : (retval < un)) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= un)) (PreH7 : (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 )) (PreH8 : (0 <= retval)) (PreH9 : (retval <= un)) (PreH10 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH11 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH12 : (a <> 0)) (PreH13 : (vals <> 0)) (PreH14 : (left <> 0)) (PreH15 : (right <> 0)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (1 <= k_pre)) (PreH18 : (k_pre <= 200000)) (PreH19 : (1 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (1 <= un)) (PreH22 : (un <= n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (0 <= ans)) (PreH26 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH27 : ((Zlength (sorted)) = n_pre)) (PreH28 : ((Zlength (keys)) = un)) (PreH29 : ((Zlength (tail)) = (n_pre - un ))) (PreH30 : ((Zlength (left_data)) = un)) (PreH31 : ((Zlength (right_data)) = un)) (PreH32 : (Permutation values sorted )) (PreH33 : (increasing sorted )) (PreH34 : (UniqueKeys sorted keys )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH36 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH37 : (0 <= ix)) (PreH38 : (ix < un)) (PreH39 : (KeyAt keys (Znth i values 0) ix )) (PreH40 : (CountingState k_pre values i keys left_data right_data ans )) (PreH41 : (1 <= (Znth ix right_data 0))) (PreH42 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH43 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH44 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
|--
  “ ((Znth (retval_2 - 0 ) keys 0) = ((Znth i values 0) * k_pre )) ” 
  &&  “ (retval_2 < un) ” 
  &&  “ ((Znth (retval - 0 ) keys 0) = ((Znth i values 0) ÷ k_pre )) ” 
  &&  “ (retval < un) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= un) ” 
  &&  “ (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= un) ” 
  &&  “ (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval ) ” 
  &&  “ (((Znth i values 0) % ( k_pre ) ) = 0) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= ((n_pre * n_pre ) * n_pre )) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < un) ” 
  &&  “ (KeyAt keys (Znth i values 0) ix ) ” 
  &&  “ (CountingState k_pre values i keys left_data right_data ans ) ” 
  &&  “ (1 <= (Znth ix right_data 0)) ” 
  &&  “ ((Znth ix right_data 0) <= (n_pre - i )) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i )))) ”
  &&  (((left + (retval * sizeof(INT64)))) # Int64  |-> (Znth retval left_data 0))
  **  (Int64Array.missing_i left retval 0 un left_data )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
.

Definition solver_partial_solve_wit_32 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth (retval_2 - 0 ) keys 0) = ((Znth i values 0) * k_pre ))) (PreH2 : (retval_2 < un)) (PreH3 : ((Znth (retval - 0 ) keys 0) = ((Znth i values 0) ÷ k_pre ))) (PreH4 : (retval < un)) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= un)) (PreH7 : (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 )) (PreH8 : (0 <= retval)) (PreH9 : (retval <= un)) (PreH10 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH11 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH12 : (a <> 0)) (PreH13 : (vals <> 0)) (PreH14 : (left <> 0)) (PreH15 : (right <> 0)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (1 <= k_pre)) (PreH18 : (k_pre <= 200000)) (PreH19 : (1 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (1 <= un)) (PreH22 : (un <= n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (0 <= ans)) (PreH26 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH27 : ((Zlength (sorted)) = n_pre)) (PreH28 : ((Zlength (keys)) = un)) (PreH29 : ((Zlength (tail)) = (n_pre - un ))) (PreH30 : ((Zlength (left_data)) = un)) (PreH31 : ((Zlength (right_data)) = un)) (PreH32 : (Permutation values sorted )) (PreH33 : (increasing sorted )) (PreH34 : (UniqueKeys sorted keys )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH36 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH37 : (0 <= ix)) (PreH38 : (ix < un)) (PreH39 : (KeyAt keys (Znth i values 0) ix )) (PreH40 : (CountingState k_pre values i keys left_data right_data ans )) (PreH41 : (1 <= (Znth ix right_data 0))) (PreH42 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH43 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH44 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full left un left_data )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
|--
  “ ((Znth (retval_2 - 0 ) keys 0) = ((Znth i values 0) * k_pre )) ” 
  &&  “ (retval_2 < un) ” 
  &&  “ ((Znth (retval - 0 ) keys 0) = ((Znth i values 0) ÷ k_pre )) ” 
  &&  “ (retval < un) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= un) ” 
  &&  “ (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= un) ” 
  &&  “ (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval ) ” 
  &&  “ (((Znth i values 0) % ( k_pre ) ) = 0) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= ((n_pre * n_pre ) * n_pre )) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < un) ” 
  &&  “ (KeyAt keys (Znth i values 0) ix ) ” 
  &&  “ (CountingState k_pre values i keys left_data right_data ans ) ” 
  &&  “ (1 <= (Znth ix right_data 0)) ” 
  &&  “ ((Znth ix right_data 0) <= (n_pre - i )) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i )))) ”
  &&  (((right + (retval_2 * sizeof(INT64)))) # Int64  |-> (Znth retval_2 (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) 0))
  **  (Int64Array.missing_i right retval_2 0 un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
.

Definition solver_partial_solve_wit_33 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth (retval_2 - 0 ) keys 0) = ((Znth i values 0) * k_pre ))) (PreH2 : (retval_2 < un)) (PreH3 : ((Znth (retval - 0 ) keys 0) = ((Znth i values 0) ÷ k_pre ))) (PreH4 : (retval < un)) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= un)) (PreH7 : (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 )) (PreH8 : (0 <= retval)) (PreH9 : (retval <= un)) (PreH10 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH11 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH12 : (a <> 0)) (PreH13 : (vals <> 0)) (PreH14 : (left <> 0)) (PreH15 : (right <> 0)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (1 <= k_pre)) (PreH18 : (k_pre <= 200000)) (PreH19 : (1 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (1 <= un)) (PreH22 : (un <= n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (0 <= ans)) (PreH26 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH27 : ((Zlength (sorted)) = n_pre)) (PreH28 : ((Zlength (keys)) = un)) (PreH29 : ((Zlength (tail)) = (n_pre - un ))) (PreH30 : ((Zlength (left_data)) = un)) (PreH31 : ((Zlength (right_data)) = un)) (PreH32 : (Permutation values sorted )) (PreH33 : (increasing sorted )) (PreH34 : (UniqueKeys sorted keys )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH36 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH37 : (0 <= ix)) (PreH38 : (ix < un)) (PreH39 : (KeyAt keys (Znth i values 0) ix )) (PreH40 : (CountingState k_pre values i keys left_data right_data ans )) (PreH41 : (1 <= (Znth ix right_data 0))) (PreH42 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH43 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH44 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
|--
  “ ((Znth (retval_2 - 0 ) keys 0) = ((Znth i values 0) * k_pre )) ” 
  &&  “ (retval_2 < un) ” 
  &&  “ ((Znth (retval - 0 ) keys 0) = ((Znth i values 0) ÷ k_pre )) ” 
  &&  “ (retval < un) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= un) ” 
  &&  “ (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= un) ” 
  &&  “ (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval ) ” 
  &&  “ (((Znth i values 0) % ( k_pre ) ) = 0) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= ((n_pre * n_pre ) * n_pre )) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < un) ” 
  &&  “ (KeyAt keys (Znth i values 0) ix ) ” 
  &&  “ (CountingState k_pre values i keys left_data right_data ans ) ” 
  &&  “ (1 <= (Znth ix right_data 0)) ” 
  &&  “ ((Znth ix right_data 0) <= (n_pre - i )) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i )))) ”
  &&  (((left + (ix * sizeof(INT64)))) # Int64  |-> (Znth ix left_data 0))
  **  (Int64Array.missing_i left ix 0 un left_data )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
.

Definition solver_partial_solve_wit_34 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth (retval_2 - 0 ) keys 0) = ((Znth i values 0) * k_pre ))) (PreH2 : (retval_2 < un)) (PreH3 : ((Znth (retval - 0 ) keys 0) = ((Znth i values 0) ÷ k_pre ))) (PreH4 : (retval < un)) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= un)) (PreH7 : (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 )) (PreH8 : (0 <= retval)) (PreH9 : (retval <= un)) (PreH10 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH11 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH12 : (a <> 0)) (PreH13 : (vals <> 0)) (PreH14 : (left <> 0)) (PreH15 : (right <> 0)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (1 <= k_pre)) (PreH18 : (k_pre <= 200000)) (PreH19 : (1 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (1 <= un)) (PreH22 : (un <= n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (0 <= ans)) (PreH26 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH27 : ((Zlength (sorted)) = n_pre)) (PreH28 : ((Zlength (keys)) = un)) (PreH29 : ((Zlength (tail)) = (n_pre - un ))) (PreH30 : ((Zlength (left_data)) = un)) (PreH31 : ((Zlength (right_data)) = un)) (PreH32 : (Permutation values sorted )) (PreH33 : (increasing sorted )) (PreH34 : (UniqueKeys sorted keys )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH36 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH37 : (0 <= ix)) (PreH38 : (ix < un)) (PreH39 : (KeyAt keys (Znth i values 0) ix )) (PreH40 : (CountingState k_pre values i keys left_data right_data ans )) (PreH41 : (1 <= (Znth ix right_data 0))) (PreH42 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH43 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH44 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full left un left_data )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
|--
  “ ((Znth (retval_2 - 0 ) keys 0) = ((Znth i values 0) * k_pre )) ” 
  &&  “ (retval_2 < un) ” 
  &&  “ ((Znth (retval - 0 ) keys 0) = ((Znth i values 0) ÷ k_pre )) ” 
  &&  “ (retval < un) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= un) ” 
  &&  “ (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= un) ” 
  &&  “ (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval ) ” 
  &&  “ (((Znth i values 0) % ( k_pre ) ) = 0) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= ((n_pre * n_pre ) * n_pre )) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < un) ” 
  &&  “ (KeyAt keys (Znth i values 0) ix ) ” 
  &&  “ (CountingState k_pre values i keys left_data right_data ans ) ” 
  &&  “ (1 <= (Znth ix right_data 0)) ” 
  &&  “ ((Znth ix right_data 0) <= (n_pre - i )) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i )))) ”
  &&  (((left + (ix * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i left ix 0 un left_data )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
.

Definition solver_partial_solve_wit_35 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 >= un)) (PreH2 : ((Znth (retval - 0 ) keys 0) = ((Znth i values 0) ÷ k_pre ))) (PreH3 : (retval < un)) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= un)) (PreH6 : (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 )) (PreH7 : (0 <= retval)) (PreH8 : (retval <= un)) (PreH9 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH10 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH11 : (a <> 0)) (PreH12 : (vals <> 0)) (PreH13 : (left <> 0)) (PreH14 : (right <> 0)) (PreH15 : (n_pre = (Zlength (values)))) (PreH16 : (1 <= k_pre)) (PreH17 : (k_pre <= 200000)) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 200000)) (PreH20 : (1 <= un)) (PreH21 : (un <= n_pre)) (PreH22 : (0 <= i)) (PreH23 : (i < n_pre)) (PreH24 : (0 <= ans)) (PreH25 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH26 : ((Zlength (sorted)) = n_pre)) (PreH27 : ((Zlength (keys)) = un)) (PreH28 : ((Zlength (tail)) = (n_pre - un ))) (PreH29 : ((Zlength (left_data)) = un)) (PreH30 : ((Zlength (right_data)) = un)) (PreH31 : (Permutation values sorted )) (PreH32 : (increasing sorted )) (PreH33 : (UniqueKeys sorted keys )) (PreH34 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH35 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH36 : (0 <= ix)) (PreH37 : (ix < un)) (PreH38 : (KeyAt keys (Znth i values 0) ix )) (PreH39 : (CountingState k_pre values i keys left_data right_data ans )) (PreH40 : (1 <= (Znth ix right_data 0))) (PreH41 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH42 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH43 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
|--
  “ (retval_2 >= un) ” 
  &&  “ ((Znth (retval - 0 ) keys 0) = ((Znth i values 0) ÷ k_pre )) ” 
  &&  “ (retval < un) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= un) ” 
  &&  “ (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= un) ” 
  &&  “ (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval ) ” 
  &&  “ (((Znth i values 0) % ( k_pre ) ) = 0) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= ((n_pre * n_pre ) * n_pre )) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < un) ” 
  &&  “ (KeyAt keys (Znth i values 0) ix ) ” 
  &&  “ (CountingState k_pre values i keys left_data right_data ans ) ” 
  &&  “ (1 <= (Znth ix right_data 0)) ” 
  &&  “ ((Znth ix right_data 0) <= (n_pre - i )) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i )))) ”
  &&  (((left + (ix * sizeof(INT64)))) # Int64  |-> (Znth ix left_data 0))
  **  (Int64Array.missing_i left ix 0 un left_data )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
.

Definition solver_partial_solve_wit_36 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 >= un)) (PreH2 : ((Znth (retval - 0 ) keys 0) = ((Znth i values 0) ÷ k_pre ))) (PreH3 : (retval < un)) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= un)) (PreH6 : (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 )) (PreH7 : (0 <= retval)) (PreH8 : (retval <= un)) (PreH9 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH10 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH11 : (a <> 0)) (PreH12 : (vals <> 0)) (PreH13 : (left <> 0)) (PreH14 : (right <> 0)) (PreH15 : (n_pre = (Zlength (values)))) (PreH16 : (1 <= k_pre)) (PreH17 : (k_pre <= 200000)) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 200000)) (PreH20 : (1 <= un)) (PreH21 : (un <= n_pre)) (PreH22 : (0 <= i)) (PreH23 : (i < n_pre)) (PreH24 : (0 <= ans)) (PreH25 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH26 : ((Zlength (sorted)) = n_pre)) (PreH27 : ((Zlength (keys)) = un)) (PreH28 : ((Zlength (tail)) = (n_pre - un ))) (PreH29 : ((Zlength (left_data)) = un)) (PreH30 : ((Zlength (right_data)) = un)) (PreH31 : (Permutation values sorted )) (PreH32 : (increasing sorted )) (PreH33 : (UniqueKeys sorted keys )) (PreH34 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH35 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH36 : (0 <= ix)) (PreH37 : (ix < un)) (PreH38 : (KeyAt keys (Znth i values 0) ix )) (PreH39 : (CountingState k_pre values i keys left_data right_data ans )) (PreH40 : (1 <= (Znth ix right_data 0))) (PreH41 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH42 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH43 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full left un left_data )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
|--
  “ (retval_2 >= un) ” 
  &&  “ ((Znth (retval - 0 ) keys 0) = ((Znth i values 0) ÷ k_pre )) ” 
  &&  “ (retval < un) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= un) ” 
  &&  “ (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= un) ” 
  &&  “ (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval ) ” 
  &&  “ (((Znth i values 0) % ( k_pre ) ) = 0) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= ((n_pre * n_pre ) * n_pre )) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < un) ” 
  &&  “ (KeyAt keys (Znth i values 0) ix ) ” 
  &&  “ (CountingState k_pre values i keys left_data right_data ans ) ” 
  &&  “ (1 <= (Znth ix right_data 0)) ” 
  &&  “ ((Znth ix right_data 0) <= (n_pre - i )) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i )))) ”
  &&  (((left + (ix * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i left ix 0 un left_data )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
.

Definition solver_partial_solve_wit_37 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval >= un)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= un)) (PreH4 : (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 )) (PreH5 : (0 <= retval)) (PreH6 : (retval <= un)) (PreH7 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH8 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH9 : (a <> 0)) (PreH10 : (vals <> 0)) (PreH11 : (left <> 0)) (PreH12 : (right <> 0)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : (1 <= k_pre)) (PreH15 : (k_pre <= 200000)) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 200000)) (PreH18 : (1 <= un)) (PreH19 : (un <= n_pre)) (PreH20 : (0 <= i)) (PreH21 : (i < n_pre)) (PreH22 : (0 <= ans)) (PreH23 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH24 : ((Zlength (sorted)) = n_pre)) (PreH25 : ((Zlength (keys)) = un)) (PreH26 : ((Zlength (tail)) = (n_pre - un ))) (PreH27 : ((Zlength (left_data)) = un)) (PreH28 : ((Zlength (right_data)) = un)) (PreH29 : (Permutation values sorted )) (PreH30 : (increasing sorted )) (PreH31 : (UniqueKeys sorted keys )) (PreH32 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH33 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH34 : (0 <= ix)) (PreH35 : (ix < un)) (PreH36 : (KeyAt keys (Znth i values 0) ix )) (PreH37 : (CountingState k_pre values i keys left_data right_data ans )) (PreH38 : (1 <= (Znth ix right_data 0))) (PreH39 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH40 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH41 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
|--
  “ (retval >= un) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= un) ” 
  &&  “ (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= un) ” 
  &&  “ (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval ) ” 
  &&  “ (((Znth i values 0) % ( k_pre ) ) = 0) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= ((n_pre * n_pre ) * n_pre )) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < un) ” 
  &&  “ (KeyAt keys (Znth i values 0) ix ) ” 
  &&  “ (CountingState k_pre values i keys left_data right_data ans ) ” 
  &&  “ (1 <= (Znth ix right_data 0)) ” 
  &&  “ ((Znth ix right_data 0) <= (n_pre - i )) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i )))) ”
  &&  (((left + (ix * sizeof(INT64)))) # Int64  |-> (Znth ix left_data 0))
  **  (Int64Array.missing_i left ix 0 un left_data )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
.

Definition solver_partial_solve_wit_38 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval >= un)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= un)) (PreH4 : (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 )) (PreH5 : (0 <= retval)) (PreH6 : (retval <= un)) (PreH7 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH8 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH9 : (a <> 0)) (PreH10 : (vals <> 0)) (PreH11 : (left <> 0)) (PreH12 : (right <> 0)) (PreH13 : (n_pre = (Zlength (values)))) (PreH14 : (1 <= k_pre)) (PreH15 : (k_pre <= 200000)) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 200000)) (PreH18 : (1 <= un)) (PreH19 : (un <= n_pre)) (PreH20 : (0 <= i)) (PreH21 : (i < n_pre)) (PreH22 : (0 <= ans)) (PreH23 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH24 : ((Zlength (sorted)) = n_pre)) (PreH25 : ((Zlength (keys)) = un)) (PreH26 : ((Zlength (tail)) = (n_pre - un ))) (PreH27 : ((Zlength (left_data)) = un)) (PreH28 : ((Zlength (right_data)) = un)) (PreH29 : (Permutation values sorted )) (PreH30 : (increasing sorted )) (PreH31 : (UniqueKeys sorted keys )) (PreH32 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH33 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH34 : (0 <= ix)) (PreH35 : (ix < un)) (PreH36 : (KeyAt keys (Znth i values 0) ix )) (PreH37 : (CountingState k_pre values i keys left_data right_data ans )) (PreH38 : (1 <= (Znth ix right_data 0))) (PreH39 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH40 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH41 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full left un left_data )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
|--
  “ (retval >= un) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= un) ” 
  &&  “ (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= un) ” 
  &&  “ (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval ) ” 
  &&  “ (((Znth i values 0) % ( k_pre ) ) = 0) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= ((n_pre * n_pre ) * n_pre )) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < un) ” 
  &&  “ (KeyAt keys (Znth i values 0) ix ) ” 
  &&  “ (CountingState k_pre values i keys left_data right_data ans ) ” 
  &&  “ (1 <= (Znth ix right_data 0)) ” 
  &&  “ ((Znth ix right_data 0) <= (n_pre - i )) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i )))) ”
  &&  (((left + (ix * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i left ix 0 un left_data )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
.

Definition solver_partial_solve_wit_39 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth (retval - 0 ) keys 0) <> ((Znth i values 0) ÷ k_pre ))) (PreH2 : (retval < un)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= un)) (PreH5 : (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 )) (PreH6 : (0 <= retval)) (PreH7 : (retval <= un)) (PreH8 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH9 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH10 : (a <> 0)) (PreH11 : (vals <> 0)) (PreH12 : (left <> 0)) (PreH13 : (right <> 0)) (PreH14 : (n_pre = (Zlength (values)))) (PreH15 : (1 <= k_pre)) (PreH16 : (k_pre <= 200000)) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 200000)) (PreH19 : (1 <= un)) (PreH20 : (un <= n_pre)) (PreH21 : (0 <= i)) (PreH22 : (i < n_pre)) (PreH23 : (0 <= ans)) (PreH24 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH25 : ((Zlength (sorted)) = n_pre)) (PreH26 : ((Zlength (keys)) = un)) (PreH27 : ((Zlength (tail)) = (n_pre - un ))) (PreH28 : ((Zlength (left_data)) = un)) (PreH29 : ((Zlength (right_data)) = un)) (PreH30 : (Permutation values sorted )) (PreH31 : (increasing sorted )) (PreH32 : (UniqueKeys sorted keys )) (PreH33 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH34 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH35 : (0 <= ix)) (PreH36 : (ix < un)) (PreH37 : (KeyAt keys (Znth i values 0) ix )) (PreH38 : (CountingState k_pre values i keys left_data right_data ans )) (PreH39 : (1 <= (Znth ix right_data 0))) (PreH40 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH41 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH42 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
|--
  “ ((Znth (retval - 0 ) keys 0) <> ((Znth i values 0) ÷ k_pre )) ” 
  &&  “ (retval < un) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= un) ” 
  &&  “ (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= un) ” 
  &&  “ (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval ) ” 
  &&  “ (((Znth i values 0) % ( k_pre ) ) = 0) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= ((n_pre * n_pre ) * n_pre )) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < un) ” 
  &&  “ (KeyAt keys (Znth i values 0) ix ) ” 
  &&  “ (CountingState k_pre values i keys left_data right_data ans ) ” 
  &&  “ (1 <= (Znth ix right_data 0)) ” 
  &&  “ ((Znth ix right_data 0) <= (n_pre - i )) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i )))) ”
  &&  (((left + (ix * sizeof(INT64)))) # Int64  |-> (Znth ix left_data 0))
  **  (Int64Array.missing_i left ix 0 un left_data )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
.

Definition solver_partial_solve_wit_40 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth (retval - 0 ) keys 0) <> ((Znth i values 0) ÷ k_pre ))) (PreH2 : (retval < un)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= un)) (PreH5 : (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 )) (PreH6 : (0 <= retval)) (PreH7 : (retval <= un)) (PreH8 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH9 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH10 : (a <> 0)) (PreH11 : (vals <> 0)) (PreH12 : (left <> 0)) (PreH13 : (right <> 0)) (PreH14 : (n_pre = (Zlength (values)))) (PreH15 : (1 <= k_pre)) (PreH16 : (k_pre <= 200000)) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 200000)) (PreH19 : (1 <= un)) (PreH20 : (un <= n_pre)) (PreH21 : (0 <= i)) (PreH22 : (i < n_pre)) (PreH23 : (0 <= ans)) (PreH24 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH25 : ((Zlength (sorted)) = n_pre)) (PreH26 : ((Zlength (keys)) = un)) (PreH27 : ((Zlength (tail)) = (n_pre - un ))) (PreH28 : ((Zlength (left_data)) = un)) (PreH29 : ((Zlength (right_data)) = un)) (PreH30 : (Permutation values sorted )) (PreH31 : (increasing sorted )) (PreH32 : (UniqueKeys sorted keys )) (PreH33 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH34 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH35 : (0 <= ix)) (PreH36 : (ix < un)) (PreH37 : (KeyAt keys (Znth i values 0) ix )) (PreH38 : (CountingState k_pre values i keys left_data right_data ans )) (PreH39 : (1 <= (Znth ix right_data 0))) (PreH40 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH41 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH42 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full left un left_data )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
|--
  “ ((Znth (retval - 0 ) keys 0) <> ((Znth i values 0) ÷ k_pre )) ” 
  &&  “ (retval < un) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= un) ” 
  &&  “ (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= un) ” 
  &&  “ (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval ) ” 
  &&  “ (((Znth i values 0) % ( k_pre ) ) = 0) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= ((n_pre * n_pre ) * n_pre )) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < un) ” 
  &&  “ (KeyAt keys (Znth i values 0) ix ) ” 
  &&  “ (CountingState k_pre values i keys left_data right_data ans ) ” 
  &&  “ (1 <= (Znth ix right_data 0)) ” 
  &&  “ ((Znth ix right_data 0) <= (n_pre - i )) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i )))) ”
  &&  (((left + (ix * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i left ix 0 un left_data )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
.

Definition solver_partial_solve_wit_41 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth (retval_2 - 0 ) keys 0) <> ((Znth i values 0) * k_pre ))) (PreH2 : (retval_2 < un)) (PreH3 : ((Znth (retval - 0 ) keys 0) = ((Znth i values 0) ÷ k_pre ))) (PreH4 : (retval < un)) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= un)) (PreH7 : (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 )) (PreH8 : (0 <= retval)) (PreH9 : (retval <= un)) (PreH10 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH11 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH12 : (a <> 0)) (PreH13 : (vals <> 0)) (PreH14 : (left <> 0)) (PreH15 : (right <> 0)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (1 <= k_pre)) (PreH18 : (k_pre <= 200000)) (PreH19 : (1 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (1 <= un)) (PreH22 : (un <= n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (0 <= ans)) (PreH26 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH27 : ((Zlength (sorted)) = n_pre)) (PreH28 : ((Zlength (keys)) = un)) (PreH29 : ((Zlength (tail)) = (n_pre - un ))) (PreH30 : ((Zlength (left_data)) = un)) (PreH31 : ((Zlength (right_data)) = un)) (PreH32 : (Permutation values sorted )) (PreH33 : (increasing sorted )) (PreH34 : (UniqueKeys sorted keys )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH36 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH37 : (0 <= ix)) (PreH38 : (ix < un)) (PreH39 : (KeyAt keys (Znth i values 0) ix )) (PreH40 : (CountingState k_pre values i keys left_data right_data ans )) (PreH41 : (1 <= (Znth ix right_data 0))) (PreH42 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH43 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH44 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
|--
  “ ((Znth (retval_2 - 0 ) keys 0) <> ((Znth i values 0) * k_pre )) ” 
  &&  “ (retval_2 < un) ” 
  &&  “ ((Znth (retval - 0 ) keys 0) = ((Znth i values 0) ÷ k_pre )) ” 
  &&  “ (retval < un) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= un) ” 
  &&  “ (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= un) ” 
  &&  “ (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval ) ” 
  &&  “ (((Znth i values 0) % ( k_pre ) ) = 0) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= ((n_pre * n_pre ) * n_pre )) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < un) ” 
  &&  “ (KeyAt keys (Znth i values 0) ix ) ” 
  &&  “ (CountingState k_pre values i keys left_data right_data ans ) ” 
  &&  “ (1 <= (Znth ix right_data 0)) ” 
  &&  “ ((Znth ix right_data 0) <= (n_pre - i )) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i )))) ”
  &&  (((left + (ix * sizeof(INT64)))) # Int64  |-> (Znth ix left_data 0))
  **  (Int64Array.missing_i left ix 0 un left_data )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
.

Definition solver_partial_solve_wit_42 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth (retval_2 - 0 ) keys 0) <> ((Znth i values 0) * k_pre ))) (PreH2 : (retval_2 < un)) (PreH3 : ((Znth (retval - 0 ) keys 0) = ((Znth i values 0) ÷ k_pre ))) (PreH4 : (retval < un)) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= un)) (PreH7 : (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 )) (PreH8 : (0 <= retval)) (PreH9 : (retval <= un)) (PreH10 : (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval )) (PreH11 : (((Znth i values 0) % ( k_pre ) ) = 0)) (PreH12 : (a <> 0)) (PreH13 : (vals <> 0)) (PreH14 : (left <> 0)) (PreH15 : (right <> 0)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (1 <= k_pre)) (PreH18 : (k_pre <= 200000)) (PreH19 : (1 <= n_pre)) (PreH20 : (n_pre <= 200000)) (PreH21 : (1 <= un)) (PreH22 : (un <= n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (0 <= ans)) (PreH26 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH27 : ((Zlength (sorted)) = n_pre)) (PreH28 : ((Zlength (keys)) = un)) (PreH29 : ((Zlength (tail)) = (n_pre - un ))) (PreH30 : ((Zlength (left_data)) = un)) (PreH31 : ((Zlength (right_data)) = un)) (PreH32 : (Permutation values sorted )) (PreH33 : (increasing sorted )) (PreH34 : (UniqueKeys sorted keys )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH36 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH37 : (0 <= ix)) (PreH38 : (ix < un)) (PreH39 : (KeyAt keys (Znth i values 0) ix )) (PreH40 : (CountingState k_pre values i keys left_data right_data ans )) (PreH41 : (1 <= (Znth ix right_data 0))) (PreH42 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH43 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH44 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full left un left_data )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
|--
  “ ((Znth (retval_2 - 0 ) keys 0) <> ((Znth i values 0) * k_pre )) ” 
  &&  “ (retval_2 < un) ” 
  &&  “ ((Znth (retval - 0 ) keys 0) = ((Znth i values 0) ÷ k_pre )) ” 
  &&  “ (retval < un) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= un) ” 
  &&  “ (LowerBoundResult keys ((Znth i values 0) * k_pre ) retval_2 ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= un) ” 
  &&  “ (LowerBoundResult keys ((Znth i values 0) ÷ k_pre ) retval ) ” 
  &&  “ (((Znth i values 0) % ( k_pre ) ) = 0) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= ((n_pre * n_pre ) * n_pre )) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < un) ” 
  &&  “ (KeyAt keys (Znth i values 0) ix ) ” 
  &&  “ (CountingState k_pre values i keys left_data right_data ans ) ” 
  &&  “ (1 <= (Znth ix right_data 0)) ” 
  &&  “ ((Znth ix right_data 0) <= (n_pre - i )) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i )))) ”
  &&  (((left + (ix * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i left ix 0 un left_data )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals un n_pre tail )
.

Definition solver_partial_solve_wit_43 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (PreH1 : (((Znth i values 0) % ( k_pre ) ) <> 0)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (left <> 0)) (PreH5 : (right <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (1 <= un)) (PreH12 : (un <= n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= ans)) (PreH16 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH17 : ((Zlength (sorted)) = n_pre)) (PreH18 : ((Zlength (keys)) = un)) (PreH19 : ((Zlength (tail)) = (n_pre - un ))) (PreH20 : ((Zlength (left_data)) = un)) (PreH21 : ((Zlength (right_data)) = un)) (PreH22 : (Permutation values sorted )) (PreH23 : (increasing sorted )) (PreH24 : (UniqueKeys sorted keys )) (PreH25 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH26 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH27 : (0 <= ix)) (PreH28 : (ix < un)) (PreH29 : (KeyAt keys (Znth i values 0) ix )) (PreH30 : (CountingState k_pre values i keys left_data right_data ans )) (PreH31 : (1 <= (Znth ix right_data 0))) (PreH32 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH33 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH34 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
  **  (Int64Array.full left un left_data )
|--
  “ (((Znth i values 0) % ( k_pre ) ) <> 0) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= ((n_pre * n_pre ) * n_pre )) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < un) ” 
  &&  “ (KeyAt keys (Znth i values 0) ix ) ” 
  &&  “ (CountingState k_pre values i keys left_data right_data ans ) ” 
  &&  “ (1 <= (Znth ix right_data 0)) ” 
  &&  “ ((Znth ix right_data 0) <= (n_pre - i )) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i )))) ”
  &&  (((left + (ix * sizeof(INT64)))) # Int64  |-> (Znth ix left_data 0))
  **  (Int64Array.missing_i left ix 0 un left_data )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
.

Definition solver_partial_solve_wit_44 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (sorted: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (a: Z) (vals: Z) (left: Z) (right: Z) (un: Z) (i: Z) (ans: Z) (ix: Z) (PreH1 : (((Znth i values 0) % ( k_pre ) ) <> 0)) (PreH2 : (a <> 0)) (PreH3 : (vals <> 0)) (PreH4 : (left <> 0)) (PreH5 : (right <> 0)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 200000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (1 <= un)) (PreH12 : (un <= n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= ans)) (PreH16 : (ans <= ((n_pre * n_pre ) * n_pre ))) (PreH17 : ((Zlength (sorted)) = n_pre)) (PreH18 : ((Zlength (keys)) = un)) (PreH19 : ((Zlength (tail)) = (n_pre - un ))) (PreH20 : ((Zlength (left_data)) = un)) (PreH21 : ((Zlength (right_data)) = un)) (PreH22 : (Permutation values sorted )) (PreH23 : (increasing sorted )) (PreH24 : (UniqueKeys sorted keys )) (PreH25 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000)))) (PreH26 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000)))) (PreH27 : (0 <= ix)) (PreH28 : (ix < un)) (PreH29 : (KeyAt keys (Znth i values 0) ix )) (PreH30 : (CountingState k_pre values i keys left_data right_data ans )) (PreH31 : (1 <= (Znth ix right_data 0))) (PreH32 : ((Znth ix right_data 0) <= (n_pre - i ))) (PreH33 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i)))) (PreH34 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i ))))) ,
  (Int64Array.full left un left_data )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
|--
  “ (((Znth i values 0) % ( k_pre ) ) <> 0) ” 
  &&  “ (a <> 0) ” 
  &&  “ (vals <> 0) ” 
  &&  “ (left <> 0) ” 
  &&  “ (right <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 200000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= un) ” 
  &&  “ (un <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= ((n_pre * n_pre ) * n_pre )) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ” 
  &&  “ (Permutation values sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (UniqueKeys sorted keys ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((-1000000000) <= (Znth j values 0)) /\ ((Znth j values 0) <= 1000000000))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < un)) -> (((-1000000000) <= (Znth j_2 keys 0)) /\ ((Znth j_2 keys 0) <= 1000000000))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < un) ” 
  &&  “ (KeyAt keys (Znth i values 0) ix ) ” 
  &&  “ (CountingState k_pre values i keys left_data right_data ans ) ” 
  &&  “ (1 <= (Znth ix right_data 0)) ” 
  &&  “ ((Znth ix right_data 0) <= (n_pre - i )) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < un)) -> ((0 <= (Znth j_3 left_data 0)) /\ ((Znth j_3 left_data 0) <= i))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < un)) -> ((0 <= (Znth j_4 right_data 0)) /\ ((Znth j_4 right_data 0) <= (n_pre - i )))) ”
  &&  (((left + (ix * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i left ix 0 un left_data )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full right un (replace_Znth (ix) (((Znth ix right_data 0) - 1 )) (right_data)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.seg vals 0 un keys )
  **  (Int64Array.seg vals un n_pre tail )
.

Definition solver_partial_solve_wit_45 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (ans: Z) (un: Z) (a: Z) (vals: Z) (left: Z) (right: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (Spec k_pre values ans )) (PreH3 : ((Zlength (keys)) = un)) (PreH4 : ((Zlength (tail)) = (n_pre - un ))) (PreH5 : ((Zlength (left_data)) = un)) (PreH6 : ((Zlength (right_data)) = un)) ,
  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full a n_pre values )
  **  (Int64Array.full vals n_pre (app (keys) (tail)) )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.full right un right_data )
|--
  “ (n_pre = (Zlength (values))) ” 
  &&  “ (Spec k_pre values ans ) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ”
  &&  (Int64Array.full a (Zlength (values)) values )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full vals n_pre (app (keys) (tail)) )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.full right un right_data )
.

Definition solver_partial_solve_wit_46 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (ans: Z) (un: Z) (vals: Z) (left: Z) (right: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (Spec k_pre values ans )) (PreH3 : ((Zlength (keys)) = un)) (PreH4 : ((Zlength (tail)) = (n_pre - un ))) (PreH5 : ((Zlength (left_data)) = un)) (PreH6 : ((Zlength (right_data)) = un)) ,
  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full vals n_pre (app (keys) (tail)) )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.full right un right_data )
|--
  “ (n_pre = (Zlength (values))) ” 
  &&  “ (Spec k_pre values ans ) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ”
  &&  (Int64Array.full vals (Zlength (values)) (app (keys) (tail)) )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.full right un right_data )
.

Definition solver_partial_solve_wit_47 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (ans: Z) (un: Z) (left: Z) (right: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (Spec k_pre values ans )) (PreH3 : ((Zlength (keys)) = un)) (PreH4 : ((Zlength (tail)) = (n_pre - un ))) (PreH5 : ((Zlength (left_data)) = un)) (PreH6 : ((Zlength (right_data)) = un)) ,
  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full left un left_data )
  **  (Int64Array.full right un right_data )
|--
  “ (n_pre = (Zlength (values))) ” 
  &&  “ (Spec k_pre values ans ) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ”
  &&  (Int64Array.full left (Zlength (keys)) left_data )
  **  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full right un right_data )
.

Definition solver_partial_solve_wit_48 := 
forall (k_pre: Z) (n_pre: Z) (input_pre: Z) (values: (@list Z)) (keys: (@list Z)) (tail: (@list Z)) (left_data: (@list Z)) (right_data: (@list Z)) (ans: Z) (un: Z) (right: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (Spec k_pre values ans )) (PreH3 : ((Zlength (keys)) = un)) (PreH4 : ((Zlength (tail)) = (n_pre - un ))) (PreH5 : ((Zlength (left_data)) = un)) (PreH6 : ((Zlength (right_data)) = un)) ,
  (Int64Array.full input_pre n_pre values )
  **  (Int64Array.full right un right_data )
|--
  “ (n_pre = (Zlength (values))) ” 
  &&  “ (Spec k_pre values ans ) ” 
  &&  “ ((Zlength (keys)) = un) ” 
  &&  “ ((Zlength (tail)) = (n_pre - un )) ” 
  &&  “ ((Zlength (left_data)) = un) ” 
  &&  “ ((Zlength (right_data)) = un) ”
  &&  (Int64Array.full right (Zlength (keys)) right_data )
  **  (Int64Array.full input_pre n_pre values )
.

Module Type VC_Correct.


Axiom proof_of_cmp_ll_safety_wit_1 : cmp_ll_safety_wit_1.
Axiom proof_of_cmp_ll_safety_wit_2 : cmp_ll_safety_wit_2.
Axiom proof_of_cmp_ll_safety_wit_3 : cmp_ll_safety_wit_3.
Axiom proof_of_cmp_ll_safety_wit_4 : cmp_ll_safety_wit_4.
Axiom proof_of_cmp_ll_return_wit_1 : cmp_ll_return_wit_1.
Axiom proof_of_cmp_ll_return_wit_2 : cmp_ll_return_wit_2.
Axiom proof_of_cmp_ll_return_wit_3 : cmp_ll_return_wit_3.
Axiom proof_of_lower_bound_ll_safety_wit_1 : lower_bound_ll_safety_wit_1.
Axiom proof_of_lower_bound_ll_safety_wit_2 : lower_bound_ll_safety_wit_2.
Axiom proof_of_lower_bound_ll_safety_wit_3 : lower_bound_ll_safety_wit_3.
Axiom proof_of_lower_bound_ll_safety_wit_4 : lower_bound_ll_safety_wit_4.
Axiom proof_of_lower_bound_ll_safety_wit_5 : lower_bound_ll_safety_wit_5.
Axiom proof_of_lower_bound_ll_safety_wit_6 : lower_bound_ll_safety_wit_6.
Axiom proof_of_lower_bound_ll_entail_wit_1 : lower_bound_ll_entail_wit_1.
Axiom proof_of_lower_bound_ll_entail_wit_2 : lower_bound_ll_entail_wit_2.
Axiom proof_of_lower_bound_ll_entail_wit_3_1 : lower_bound_ll_entail_wit_3_1.
Axiom proof_of_lower_bound_ll_entail_wit_3_2 : lower_bound_ll_entail_wit_3_2.
Axiom proof_of_lower_bound_ll_return_wit_1 : lower_bound_ll_return_wit_1.
Axiom proof_of_lower_bound_ll_partial_solve_wit_1 : lower_bound_ll_partial_solve_wit_1.
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Axiom proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Axiom proof_of_solver_entail_wit_5_3 : solver_entail_wit_5_3.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Axiom proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Axiom proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Axiom proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Axiom proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Axiom proof_of_solver_entail_wit_12_1 : solver_entail_wit_12_1.
Axiom proof_of_solver_entail_wit_12_2 : solver_entail_wit_12_2.
Axiom proof_of_solver_entail_wit_12_3 : solver_entail_wit_12_3.
Axiom proof_of_solver_entail_wit_12_4 : solver_entail_wit_12_4.
Axiom proof_of_solver_entail_wit_12_5 : solver_entail_wit_12_5.
Axiom proof_of_solver_entail_wit_12_6 : solver_entail_wit_12_6.
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
Axiom proof_of_solver_partial_solve_wit_11 : solver_partial_solve_wit_11.
Axiom proof_of_solver_partial_solve_wit_12 : solver_partial_solve_wit_12.
Axiom proof_of_solver_partial_solve_wit_13 : solver_partial_solve_wit_13.
Axiom proof_of_solver_partial_solve_wit_14_pure : solver_partial_solve_wit_14_pure.
Axiom proof_of_solver_partial_solve_wit_14 : solver_partial_solve_wit_14.
Axiom proof_of_solver_partial_solve_wit_15_pure : solver_partial_solve_wit_15_pure.
Axiom proof_of_solver_partial_solve_wit_15 : solver_partial_solve_wit_15.
Axiom proof_of_solver_partial_solve_wit_16 : solver_partial_solve_wit_16.
Axiom proof_of_solver_partial_solve_wit_17_pure : solver_partial_solve_wit_17_pure.
Axiom proof_of_solver_partial_solve_wit_17 : solver_partial_solve_wit_17.
Axiom proof_of_solver_partial_solve_wit_18 : solver_partial_solve_wit_18.
Axiom proof_of_solver_partial_solve_wit_19 : solver_partial_solve_wit_19.
Axiom proof_of_solver_partial_solve_wit_20 : solver_partial_solve_wit_20.
Axiom proof_of_solver_partial_solve_wit_21_pure : solver_partial_solve_wit_21_pure.
Axiom proof_of_solver_partial_solve_wit_21 : solver_partial_solve_wit_21.
Axiom proof_of_solver_partial_solve_wit_22 : solver_partial_solve_wit_22.
Axiom proof_of_solver_partial_solve_wit_23 : solver_partial_solve_wit_23.
Axiom proof_of_solver_partial_solve_wit_24 : solver_partial_solve_wit_24.
Axiom proof_of_solver_partial_solve_wit_25 : solver_partial_solve_wit_25.
Axiom proof_of_solver_partial_solve_wit_26 : solver_partial_solve_wit_26.
Axiom proof_of_solver_partial_solve_wit_27_pure : solver_partial_solve_wit_27_pure.
Axiom proof_of_solver_partial_solve_wit_27 : solver_partial_solve_wit_27.
Axiom proof_of_solver_partial_solve_wit_28_pure : solver_partial_solve_wit_28_pure.
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
Axiom proof_of_solver_partial_solve_wit_43 : solver_partial_solve_wit_43.
Axiom proof_of_solver_partial_solve_wit_44 : solver_partial_solve_wit_44.
Axiom proof_of_solver_partial_solve_wit_45 : solver_partial_solve_wit_45.
Axiom proof_of_solver_partial_solve_wit_46 : solver_partial_solve_wit_46.
Axiom proof_of_solver_partial_solve_wit_47 : solver_partial_solve_wit_47.
Axiom proof_of_solver_partial_solve_wit_48 : solver_partial_solve_wit_48.

End VC_Correct.
