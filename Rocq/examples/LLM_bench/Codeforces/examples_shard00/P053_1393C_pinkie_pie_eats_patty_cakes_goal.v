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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (PreH1 : (2 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= (Zlength (values)))))) (PreH4 : (Pre values )) (PreH5 : (n_pre = (Zlength (values)))) ,
  ((( &( "cnt" ) )) # Ptr  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_2 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 100000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= (Zlength (values)))))) (PreH5 : (Pre values )) (PreH6 : (n_pre = (Zlength (values)))) ,
  ((( &( "mx" ) )) # Int  |->_)
  **  (IntArray.full retval (n_pre + 1 ) (repeat_Z (0) ((n_pre + 1 ))) )
  **  ((( &( "cnt" ) )) # Ptr  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 100000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= (Zlength (values)))))) (PreH5 : (Pre values )) (PreH6 : (n_pre = (Zlength (values)))) ,
  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "mx" ) )) # Int  |-> 0)
  **  (IntArray.full retval (n_pre + 1 ) (repeat_Z (0) ((n_pre + 1 ))) )
  **  ((( &( "cnt" ) )) # Ptr  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 100000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= (Zlength (values)))))) (PreH5 : (Pre values )) (PreH6 : (n_pre = (Zlength (values)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "c" ) )) # Int  |-> 0)
  **  ((( &( "mx" ) )) # Int  |-> 0)
  **  (IntArray.full retval (n_pre + 1 ) (repeat_Z (0) ((n_pre + 1 ))) )
  **  ((( &( "cnt" ) )) # Ptr  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_5 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (counts: (@list Z)) (i: Z) (c: Z) (mx: Z) (cnt: Z) (PreH1 : (i < n_pre)) (PreH2 : (cnt <> 0)) (PreH3 : (mx = 0)) (PreH4 : (c = 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH9 : (Pre values )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (CountPrefix values i counts )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= i)))) ,
  (IntArray.full cnt (n_pre + 1 ) counts )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt)
  **  ((( &( "mx" ) )) # Int  |-> mx)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (((Znth (Znth i values 0) counts 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (Znth i values 0) counts 0) + 1 )) ”
.

Definition solver_safety_wit_6 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (counts: (@list Z)) (i: Z) (c: Z) (mx: Z) (cnt: Z) (PreH1 : (i < n_pre)) (PreH2 : (cnt <> 0)) (PreH3 : (mx = 0)) (PreH4 : (c = 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH9 : (Pre values )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (CountPrefix values i counts )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= i)))) ,
  (IntArray.full cnt (n_pre + 1 ) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) counts 0) + 1 )) (counts)) )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt)
  **  ((( &( "mx" ) )) # Int  |-> mx)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_7 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (counts: (@list Z)) (i: Z) (c: Z) (mx: Z) (cnt: Z) (PreH1 : (i >= n_pre)) (PreH2 : (cnt <> 0)) (PreH3 : (mx = 0)) (PreH4 : (c = 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH9 : (Pre values )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (CountPrefix values i counts )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= i)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt)
  **  ((( &( "mx" ) )) # Int  |-> mx)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full cnt (n_pre + 1 ) counts )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_8 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (counts: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : ((Znth i counts 0) > mx)) (PreH2 : (i <= n_pre)) (PreH3 : (cnt <> 0)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH8 : (Pre values )) (PreH9 : (1 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (0 <= mx)) (PreH12 : (mx <= n_pre)) (PreH13 : (0 <= c)) (PreH14 : (c <= (i - 1 ))) (PreH15 : (CountPrefix values n_pre counts )) (PreH16 : (MaximumFrequencyPrefix counts i mx c )) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= n_pre)))) ,
  (IntArray.full cnt (n_pre + 1 ) counts )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mx" ) )) # Int  |-> (Znth i counts 0))
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_9 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (counts: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : ((Znth i counts 0) = mx)) (PreH2 : ((Znth i counts 0) <= mx)) (PreH3 : (i <= n_pre)) (PreH4 : (cnt <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH9 : (Pre values )) (PreH10 : (1 <= i)) (PreH11 : (i <= (n_pre + 1 ))) (PreH12 : (0 <= mx)) (PreH13 : (mx <= n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c <= (i - 1 ))) (PreH16 : (CountPrefix values n_pre counts )) (PreH17 : (MaximumFrequencyPrefix counts i mx c )) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= n_pre)))) ,
  (IntArray.full cnt (n_pre + 1 ) counts )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mx" ) )) # Int  |-> mx)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((c + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (c + 1 )) ”
.

Definition solver_safety_wit_10 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (counts: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : ((Znth i counts 0) > mx)) (PreH2 : (i <= n_pre)) (PreH3 : (cnt <> 0)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH8 : (Pre values )) (PreH9 : (1 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (0 <= mx)) (PreH12 : (mx <= n_pre)) (PreH13 : (0 <= c)) (PreH14 : (c <= (i - 1 ))) (PreH15 : (CountPrefix values n_pre counts )) (PreH16 : (MaximumFrequencyPrefix counts i mx c )) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= n_pre)))) ,
  (IntArray.full cnt (n_pre + 1 ) counts )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mx" ) )) # Int  |-> (Znth i counts 0))
  **  ((( &( "c" ) )) # Int  |-> 1)
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_11 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (counts: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : ((Znth i counts 0) = mx)) (PreH2 : ((Znth i counts 0) <= mx)) (PreH3 : (i <= n_pre)) (PreH4 : (cnt <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH9 : (Pre values )) (PreH10 : (1 <= i)) (PreH11 : (i <= (n_pre + 1 ))) (PreH12 : (0 <= mx)) (PreH13 : (mx <= n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c <= (i - 1 ))) (PreH16 : (CountPrefix values n_pre counts )) (PreH17 : (MaximumFrequencyPrefix counts i mx c )) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= n_pre)))) ,
  (IntArray.full cnt (n_pre + 1 ) counts )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mx" ) )) # Int  |-> mx)
  **  ((( &( "c" ) )) # Int  |-> (c + 1 ))
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_12 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (counts: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : ((Znth i counts 0) <> mx)) (PreH2 : ((Znth i counts 0) <= mx)) (PreH3 : (i <= n_pre)) (PreH4 : (cnt <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH9 : (Pre values )) (PreH10 : (1 <= i)) (PreH11 : (i <= (n_pre + 1 ))) (PreH12 : (0 <= mx)) (PreH13 : (mx <= n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c <= (i - 1 ))) (PreH16 : (CountPrefix values n_pre counts )) (PreH17 : (MaximumFrequencyPrefix counts i mx c )) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= n_pre)))) ,
  (IntArray.full cnt (n_pre + 1 ) counts )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "mx" ) )) # Int  |-> mx)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_13 := 
(
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (counts: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : (i > n_pre)) (PreH2 : (cnt <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH7 : (Pre values )) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1 ))) (PreH10 : (0 <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : (0 <= c)) (PreH13 : (c <= (i - 1 ))) (PreH14 : (CountPrefix values n_pre counts )) (PreH15 : (MaximumFrequencyPrefix counts i mx c )) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= n_pre)))) ,
  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt)
  **  ((( &( "mx" ) )) # Int  |-> mx)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full cnt (n_pre + 1 ) counts )
|--
  “ ((((n_pre - c ) ÷ (mx - 1 ) ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((n_pre - c ) ÷ (mx - 1 ) ) - 1 )) ”
) \/
(
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (counts: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : (i > n_pre)) (PreH2 : (cnt <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH7 : (Pre values )) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1 ))) (PreH10 : (0 <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : (0 <= c)) (PreH13 : (c <= (i - 1 ))) (PreH14 : (CountPrefix values n_pre counts )) (PreH15 : (MaximumFrequencyPrefix counts i mx c )) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= n_pre)))) ,
  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt)
  **  ((( &( "mx" ) )) # Int  |-> mx)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full cnt (n_pre + 1 ) counts )
|--
  “ ((((n_pre - c ) ÷ (mx - 1 ) ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((n_pre - c ) ÷ (mx - 1 ) ) - 1 )) ”
).

Definition solver_safety_wit_13_split_goal_1 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (counts: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : (i > n_pre)) (PreH2 : (cnt <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH7 : (Pre values )) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1 ))) (PreH10 : (0 <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : (0 <= c)) (PreH13 : (c <= (i - 1 ))) (PreH14 : (CountPrefix values n_pre counts )) (PreH15 : (MaximumFrequencyPrefix counts i mx c )) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= n_pre)))) ,
  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt)
  **  ((( &( "mx" ) )) # Int  |-> mx)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full cnt (n_pre + 1 ) counts )
|--
  “ ((((n_pre - c ) ÷ (mx - 1 ) ) - 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_13_split_goal_2 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (counts: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : (i > n_pre)) (PreH2 : (cnt <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH7 : (Pre values )) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1 ))) (PreH10 : (0 <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : (0 <= c)) (PreH13 : (c <= (i - 1 ))) (PreH14 : (CountPrefix values n_pre counts )) (PreH15 : (MaximumFrequencyPrefix counts i mx c )) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= n_pre)))) ,
  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt)
  **  ((( &( "mx" ) )) # Int  |-> mx)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full cnt (n_pre + 1 ) counts )
|--
  “ ((INT_MIN) <= (((n_pre - c ) ÷ (mx - 1 ) ) - 1 )) ”
.

Definition solver_safety_wit_14 := 
(
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (counts: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : (i > n_pre)) (PreH2 : (cnt <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH7 : (Pre values )) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1 ))) (PreH10 : (0 <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : (0 <= c)) (PreH13 : (c <= (i - 1 ))) (PreH14 : (CountPrefix values n_pre counts )) (PreH15 : (MaximumFrequencyPrefix counts i mx c )) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= n_pre)))) ,
  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt)
  **  ((( &( "mx" ) )) # Int  |-> mx)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full cnt (n_pre + 1 ) counts )
|--
  “ (((n_pre - c ) <> (INT_MIN)) \/ ((mx - 1 ) <> (-1))) ” 
  &&  “ ((mx - 1 ) <> 0) ”
) \/
(
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (counts: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : (i > n_pre)) (PreH2 : (cnt <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH7 : (Pre values )) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1 ))) (PreH10 : (0 <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : (0 <= c)) (PreH13 : (c <= (i - 1 ))) (PreH14 : (CountPrefix values n_pre counts )) (PreH15 : (MaximumFrequencyPrefix counts i mx c )) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= n_pre)))) ,
  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt)
  **  ((( &( "mx" ) )) # Int  |-> mx)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full cnt (n_pre + 1 ) counts )
|--
  “ (((n_pre - c ) <> (INT_MIN)) \/ ((mx - 1 ) <> (-1))) ” 
  &&  “ ((mx - 1 ) <> 0) ”
).

Definition solver_safety_wit_14_split_goal_1 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (counts: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : (i > n_pre)) (PreH2 : (cnt <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH7 : (Pre values )) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1 ))) (PreH10 : (0 <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : (0 <= c)) (PreH13 : (c <= (i - 1 ))) (PreH14 : (CountPrefix values n_pre counts )) (PreH15 : (MaximumFrequencyPrefix counts i mx c )) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= n_pre)))) ,
  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt)
  **  ((( &( "mx" ) )) # Int  |-> mx)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full cnt (n_pre + 1 ) counts )
|--
  “ (((n_pre - c ) <> (INT_MIN)) \/ ((mx - 1 ) <> (-1))) ”
.

Definition solver_safety_wit_14_split_goal_2 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (counts: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : (i > n_pre)) (PreH2 : (cnt <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH7 : (Pre values )) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1 ))) (PreH10 : (0 <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : (0 <= c)) (PreH13 : (c <= (i - 1 ))) (PreH14 : (CountPrefix values n_pre counts )) (PreH15 : (MaximumFrequencyPrefix counts i mx c )) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= n_pre)))) ,
  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt)
  **  ((( &( "mx" ) )) # Int  |-> mx)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full cnt (n_pre + 1 ) counts )
|--
  “ ((mx - 1 ) <> 0) ”
.

Definition solver_safety_wit_15 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (counts: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : (i > n_pre)) (PreH2 : (cnt <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH7 : (Pre values )) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1 ))) (PreH10 : (0 <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : (0 <= c)) (PreH13 : (c <= (i - 1 ))) (PreH14 : (CountPrefix values n_pre counts )) (PreH15 : (MaximumFrequencyPrefix counts i mx c )) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= n_pre)))) ,
  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt)
  **  ((( &( "mx" ) )) # Int  |-> mx)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full cnt (n_pre + 1 ) counts )
|--
  “ ((mx - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (mx - 1 )) ”
.

Definition solver_safety_wit_16 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (counts: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : (i > n_pre)) (PreH2 : (cnt <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH7 : (Pre values )) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1 ))) (PreH10 : (0 <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : (0 <= c)) (PreH13 : (c <= (i - 1 ))) (PreH14 : (CountPrefix values n_pre counts )) (PreH15 : (MaximumFrequencyPrefix counts i mx c )) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= n_pre)))) ,
  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt)
  **  ((( &( "mx" ) )) # Int  |-> mx)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full cnt (n_pre + 1 ) counts )
|--
  “ ((n_pre - c ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - c )) ”
.

Definition solver_safety_wit_17 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (counts: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : (i > n_pre)) (PreH2 : (cnt <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH7 : (Pre values )) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1 ))) (PreH10 : (0 <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : (0 <= c)) (PreH13 : (c <= (i - 1 ))) (PreH14 : (CountPrefix values n_pre counts )) (PreH15 : (MaximumFrequencyPrefix counts i mx c )) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= n_pre)))) ,
  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt)
  **  ((( &( "mx" ) )) # Int  |-> mx)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full cnt (n_pre + 1 ) counts )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_18 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (counts: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : (i > n_pre)) (PreH2 : (cnt <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH7 : (Pre values )) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1 ))) (PreH10 : (0 <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : (0 <= c)) (PreH13 : (c <= (i - 1 ))) (PreH14 : (CountPrefix values n_pre counts )) (PreH15 : (MaximumFrequencyPrefix counts i mx c )) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= n_pre)))) ,
  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # Ptr  |-> cnt)
  **  ((( &( "mx" ) )) # Int  |-> mx)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full cnt (n_pre + 1 ) counts )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_entail_wit_1 := 
(
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 100000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= (Zlength (values)))))) (PreH5 : (Pre values )) (PreH6 : (n_pre = (Zlength (values)))) ,
  (IntArray.full retval (n_pre + 1 ) (repeat_Z (0) ((n_pre + 1 ))) )
  **  (IntArray.full a_pre n_pre values )
|--
  EX (counts: (@list Z)) ,
  “ (retval <> 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (2 <= (Zlength (values))) ” 
  &&  “ ((Zlength (values)) <= 100000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values))))) ” 
  &&  “ (Pre values ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (CountPrefix values 0 counts ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= 0))) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full retval (n_pre + 1 ) counts )
) \/
(
forall (n_pre: Z) (values: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 100000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= (Zlength (values)))))) (PreH5 : (Pre values )) (PreH6 : (n_pre = (Zlength (values)))) ,
  TT && emp 
|--
  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 (repeat_Z (0) ((n_pre + 1 ))) 0)) /\ ((Znth k_2 (repeat_Z (0) ((n_pre + 1 ))) 0) <= 0))) ” 
  &&  “ (CountPrefix values 0 (repeat_Z (0) ((n_pre + 1 ))) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values))))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (values: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 100000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= (Zlength (values)))))) (PreH5 : (Pre values )) (PreH6 : (n_pre = (Zlength (values)))) ,
  forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 (repeat_Z (0) ((n_pre + 1 ))) 0)) /\ ((Znth k_2 (repeat_Z (0) ((n_pre + 1 ))) 0) <= 0)))
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (values: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 100000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= (Zlength (values)))))) (PreH5 : (Pre values )) (PreH6 : (n_pre = (Zlength (values)))) ,
  (CountPrefix values 0 (repeat_Z (0) ((n_pre + 1 ))) )
.

Definition solver_entail_wit_1_split_goal_3 := 
forall (n_pre: Z) (values: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (2 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 100000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= (Zlength (values)))))) (PreH5 : (Pre values )) (PreH6 : (n_pre = (Zlength (values)))) ,
  forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))
.

Definition solver_entail_wit_2 := 
(
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (counts_2: (@list Z)) (i: Z) (c: Z) (mx: Z) (cnt: Z) (PreH1 : (i < n_pre)) (PreH2 : (cnt <> 0)) (PreH3 : (mx = 0)) (PreH4 : (c = 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH9 : (Pre values )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (CountPrefix values i counts_2 )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts_2 0)) /\ ((Znth k_2 counts_2 0) <= i)))) ,
  (IntArray.full cnt (n_pre + 1 ) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) counts_2 0) + 1 )) (counts_2)) )
  **  (IntArray.full a_pre n_pre values )
|--
  EX (counts: (@list Z)) ,
  “ (cnt <> 0) ” 
  &&  “ (mx = 0) ” 
  &&  “ (c = 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (2 <= (Zlength (values))) ” 
  &&  “ ((Zlength (values)) <= 100000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values))))) ” 
  &&  “ (Pre values ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (CountPrefix values (i + 1 ) counts ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= (i + 1 )))) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full cnt (n_pre + 1 ) counts )
) \/
(
forall (n_pre: Z) (values: (@list Z)) (counts_2: (@list Z)) (i: Z) (c: Z) (mx: Z) (cnt: Z) (PreH1 : (i < n_pre)) (PreH2 : (cnt <> 0)) (PreH3 : (mx = 0)) (PreH4 : (c = 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH9 : (Pre values )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (CountPrefix values i counts_2 )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts_2 0)) /\ ((Znth k_2 counts_2 0) <= i)))) ,
  TT && emp 
|--
  “ (CountPrefix values (i + 1 ) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) counts_2 0) + 1 )) (counts_2)) ) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (values: (@list Z)) (counts_2: (@list Z)) (i: Z) (c: Z) (mx: Z) (cnt: Z) (PreH1 : (i < n_pre)) (PreH2 : (cnt <> 0)) (PreH3 : (mx = 0)) (PreH4 : (c = 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH9 : (Pre values )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (CountPrefix values i counts_2 )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts_2 0)) /\ ((Znth k_2 counts_2 0) <= i)))) ,
  (CountPrefix values (i + 1 ) (replace_Znth ((Znth i values 0)) (((Znth (Znth i values 0) counts_2 0) + 1 )) (counts_2)) )
.

Definition solver_entail_wit_3 := 
(
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (counts_2: (@list Z)) (i: Z) (c: Z) (mx: Z) (cnt: Z) (PreH1 : (i >= n_pre)) (PreH2 : (cnt <> 0)) (PreH3 : (mx = 0)) (PreH4 : (c = 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= (Zlength (values)))))) (PreH9 : (Pre values )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (CountPrefix values i counts_2 )) (PreH13 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 counts_2 0)) /\ ((Znth k_4 counts_2 0) <= i)))) ,
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full cnt (n_pre + 1 ) counts_2 )
|--
  EX (counts: (@list Z)) ,
  “ (cnt <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (2 <= (Zlength (values))) ” 
  &&  “ ((Zlength (values)) <= 100000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values))))) ” 
  &&  “ (Pre values ) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c <= (1 - 1 )) ” 
  &&  “ (CountPrefix values n_pre counts ) ” 
  &&  “ (MaximumFrequencyPrefix counts 1 mx c ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= n_pre))) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full cnt (n_pre + 1 ) counts )
) \/
(
forall (n_pre: Z) (values: (@list Z)) (counts_2: (@list Z)) (i: Z) (c: Z) (mx: Z) (cnt: Z) (PreH1 : (i >= n_pre)) (PreH2 : (cnt <> 0)) (PreH3 : (mx = 0)) (PreH4 : (c = 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= (Zlength (values)))))) (PreH9 : (Pre values )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (CountPrefix values i counts_2 )) (PreH13 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 counts_2 0)) /\ ((Znth k_4 counts_2 0) <= i)))) ,
  TT && emp 
|--
  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts_2 0)) /\ ((Znth k_2 counts_2 0) <= n_pre))) ” 
  &&  “ (MaximumFrequencyPrefix counts_2 1 0 0 ) ” 
  &&  “ (CountPrefix values n_pre counts_2 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values))))) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 := 
forall (n_pre: Z) (values: (@list Z)) (counts_2: (@list Z)) (i: Z) (c: Z) (mx: Z) (cnt: Z) (PreH1 : (i >= n_pre)) (PreH2 : (cnt <> 0)) (PreH3 : (mx = 0)) (PreH4 : (c = 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= (Zlength (values)))))) (PreH9 : (Pre values )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (CountPrefix values i counts_2 )) (PreH13 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 counts_2 0)) /\ ((Znth k_4 counts_2 0) <= i)))) ,
  forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts_2 0)) /\ ((Znth k_2 counts_2 0) <= n_pre)))
.

Definition solver_entail_wit_3_split_goal_2 := 
forall (n_pre: Z) (values: (@list Z)) (counts_2: (@list Z)) (i: Z) (c: Z) (mx: Z) (cnt: Z) (PreH1 : (i >= n_pre)) (PreH2 : (cnt <> 0)) (PreH3 : (mx = 0)) (PreH4 : (c = 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= (Zlength (values)))))) (PreH9 : (Pre values )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (CountPrefix values i counts_2 )) (PreH13 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 counts_2 0)) /\ ((Znth k_4 counts_2 0) <= i)))) ,
  (MaximumFrequencyPrefix counts_2 1 0 0 )
.

Definition solver_entail_wit_3_split_goal_3 := 
forall (n_pre: Z) (values: (@list Z)) (counts_2: (@list Z)) (i: Z) (c: Z) (mx: Z) (cnt: Z) (PreH1 : (i >= n_pre)) (PreH2 : (cnt <> 0)) (PreH3 : (mx = 0)) (PreH4 : (c = 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= (Zlength (values)))))) (PreH9 : (Pre values )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (CountPrefix values i counts_2 )) (PreH13 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 counts_2 0)) /\ ((Znth k_4 counts_2 0) <= i)))) ,
  (CountPrefix values n_pre counts_2 )
.

Definition solver_entail_wit_3_split_goal_4 := 
forall (n_pre: Z) (values: (@list Z)) (counts_2: (@list Z)) (i: Z) (c: Z) (mx: Z) (cnt: Z) (PreH1 : (i >= n_pre)) (PreH2 : (cnt <> 0)) (PreH3 : (mx = 0)) (PreH4 : (c = 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= (Zlength (values)))))) (PreH9 : (Pre values )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (CountPrefix values i counts_2 )) (PreH13 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 counts_2 0)) /\ ((Znth k_4 counts_2 0) <= i)))) ,
  forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))
.

Definition solver_entail_wit_4_1 := 
(
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (counts_2: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : ((Znth i counts_2 0) > mx)) (PreH2 : (i <= n_pre)) (PreH3 : (cnt <> 0)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH8 : (Pre values )) (PreH9 : (1 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (0 <= mx)) (PreH12 : (mx <= n_pre)) (PreH13 : (0 <= c)) (PreH14 : (c <= (i - 1 ))) (PreH15 : (CountPrefix values n_pre counts_2 )) (PreH16 : (MaximumFrequencyPrefix counts_2 i mx c )) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts_2 0)) /\ ((Znth k_2 counts_2 0) <= n_pre)))) ,
  (IntArray.full cnt (n_pre + 1 ) counts_2 )
  **  (IntArray.full a_pre n_pre values )
|--
  EX (counts: (@list Z)) ,
  “ (cnt <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (2 <= (Zlength (values))) ” 
  &&  “ ((Zlength (values)) <= 100000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values))))) ” 
  &&  “ (Pre values ) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (0 <= (Znth i counts_2 0)) ” 
  &&  “ ((Znth i counts_2 0) <= n_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= ((i + 1 ) - 1 )) ” 
  &&  “ (CountPrefix values n_pre counts ) ” 
  &&  “ (MaximumFrequencyPrefix counts (i + 1 ) (Znth i counts_2 0) 1 ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= n_pre))) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full cnt (n_pre + 1 ) counts )
) \/
(
forall (n_pre: Z) (values: (@list Z)) (counts_2: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : ((Znth i counts_2 0) > mx)) (PreH2 : (i <= n_pre)) (PreH3 : (cnt <> 0)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH8 : (Pre values )) (PreH9 : (1 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (0 <= mx)) (PreH12 : (mx <= n_pre)) (PreH13 : (0 <= c)) (PreH14 : (c <= (i - 1 ))) (PreH15 : (CountPrefix values n_pre counts_2 )) (PreH16 : (MaximumFrequencyPrefix counts_2 i mx c )) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts_2 0)) /\ ((Znth k_2 counts_2 0) <= n_pre)))) ,
  TT && emp 
|--
  “ (MaximumFrequencyPrefix counts_2 (i + 1 ) (Znth i counts_2 0) 1 ) ”
  &&  emp
).

Definition solver_entail_wit_4_1_split_goal_1 := 
forall (n_pre: Z) (values: (@list Z)) (counts_2: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : ((Znth i counts_2 0) > mx)) (PreH2 : (i <= n_pre)) (PreH3 : (cnt <> 0)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH8 : (Pre values )) (PreH9 : (1 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (0 <= mx)) (PreH12 : (mx <= n_pre)) (PreH13 : (0 <= c)) (PreH14 : (c <= (i - 1 ))) (PreH15 : (CountPrefix values n_pre counts_2 )) (PreH16 : (MaximumFrequencyPrefix counts_2 i mx c )) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts_2 0)) /\ ((Znth k_2 counts_2 0) <= n_pre)))) ,
  (MaximumFrequencyPrefix counts_2 (i + 1 ) (Znth i counts_2 0) 1 )
.

Definition solver_entail_wit_4_2 := 
(
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (counts_2: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : ((Znth i counts_2 0) = mx)) (PreH2 : ((Znth i counts_2 0) <= mx)) (PreH3 : (i <= n_pre)) (PreH4 : (cnt <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH9 : (Pre values )) (PreH10 : (1 <= i)) (PreH11 : (i <= (n_pre + 1 ))) (PreH12 : (0 <= mx)) (PreH13 : (mx <= n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c <= (i - 1 ))) (PreH16 : (CountPrefix values n_pre counts_2 )) (PreH17 : (MaximumFrequencyPrefix counts_2 i mx c )) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts_2 0)) /\ ((Znth k_2 counts_2 0) <= n_pre)))) ,
  (IntArray.full cnt (n_pre + 1 ) counts_2 )
  **  (IntArray.full a_pre n_pre values )
|--
  EX (counts: (@list Z)) ,
  “ (cnt <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (2 <= (Zlength (values))) ” 
  &&  “ ((Zlength (values)) <= 100000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values))))) ” 
  &&  “ (Pre values ) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= n_pre) ” 
  &&  “ (0 <= (c + 1 )) ” 
  &&  “ ((c + 1 ) <= ((i + 1 ) - 1 )) ” 
  &&  “ (CountPrefix values n_pre counts ) ” 
  &&  “ (MaximumFrequencyPrefix counts (i + 1 ) mx (c + 1 ) ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= n_pre))) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full cnt (n_pre + 1 ) counts )
) \/
(
forall (n_pre: Z) (values: (@list Z)) (counts_2: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : ((Znth i counts_2 0) = mx)) (PreH2 : ((Znth i counts_2 0) <= mx)) (PreH3 : (i <= n_pre)) (PreH4 : (cnt <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH9 : (Pre values )) (PreH10 : (1 <= i)) (PreH11 : (i <= (n_pre + 1 ))) (PreH12 : (0 <= mx)) (PreH13 : (mx <= n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c <= (i - 1 ))) (PreH16 : (CountPrefix values n_pre counts_2 )) (PreH17 : (MaximumFrequencyPrefix counts_2 i mx c )) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts_2 0)) /\ ((Znth k_2 counts_2 0) <= n_pre)))) ,
  TT && emp 
|--
  “ (MaximumFrequencyPrefix counts_2 (i + 1 ) mx (c + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_4_2_split_goal_1 := 
forall (n_pre: Z) (values: (@list Z)) (counts_2: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : ((Znth i counts_2 0) = mx)) (PreH2 : ((Znth i counts_2 0) <= mx)) (PreH3 : (i <= n_pre)) (PreH4 : (cnt <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH9 : (Pre values )) (PreH10 : (1 <= i)) (PreH11 : (i <= (n_pre + 1 ))) (PreH12 : (0 <= mx)) (PreH13 : (mx <= n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c <= (i - 1 ))) (PreH16 : (CountPrefix values n_pre counts_2 )) (PreH17 : (MaximumFrequencyPrefix counts_2 i mx c )) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts_2 0)) /\ ((Znth k_2 counts_2 0) <= n_pre)))) ,
  (MaximumFrequencyPrefix counts_2 (i + 1 ) mx (c + 1 ) )
.

Definition solver_entail_wit_4_3 := 
(
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (counts_2: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : ((Znth i counts_2 0) <> mx)) (PreH2 : ((Znth i counts_2 0) <= mx)) (PreH3 : (i <= n_pre)) (PreH4 : (cnt <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH9 : (Pre values )) (PreH10 : (1 <= i)) (PreH11 : (i <= (n_pre + 1 ))) (PreH12 : (0 <= mx)) (PreH13 : (mx <= n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c <= (i - 1 ))) (PreH16 : (CountPrefix values n_pre counts_2 )) (PreH17 : (MaximumFrequencyPrefix counts_2 i mx c )) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts_2 0)) /\ ((Znth k_2 counts_2 0) <= n_pre)))) ,
  (IntArray.full cnt (n_pre + 1 ) counts_2 )
  **  (IntArray.full a_pre n_pre values )
|--
  EX (counts: (@list Z)) ,
  “ (cnt <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (2 <= (Zlength (values))) ” 
  &&  “ ((Zlength (values)) <= 100000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values))))) ” 
  &&  “ (Pre values ) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c <= ((i + 1 ) - 1 )) ” 
  &&  “ (CountPrefix values n_pre counts ) ” 
  &&  “ (MaximumFrequencyPrefix counts (i + 1 ) mx c ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= n_pre))) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full cnt (n_pre + 1 ) counts )
) \/
(
forall (n_pre: Z) (values: (@list Z)) (counts_2: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : ((Znth i counts_2 0) <> mx)) (PreH2 : ((Znth i counts_2 0) <= mx)) (PreH3 : (i <= n_pre)) (PreH4 : (cnt <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH9 : (Pre values )) (PreH10 : (1 <= i)) (PreH11 : (i <= (n_pre + 1 ))) (PreH12 : (0 <= mx)) (PreH13 : (mx <= n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c <= (i - 1 ))) (PreH16 : (CountPrefix values n_pre counts_2 )) (PreH17 : (MaximumFrequencyPrefix counts_2 i mx c )) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts_2 0)) /\ ((Znth k_2 counts_2 0) <= n_pre)))) ,
  TT && emp 
|--
  “ (MaximumFrequencyPrefix counts_2 (i + 1 ) mx c ) ”
  &&  emp
).

Definition solver_entail_wit_4_3_split_goal_1 := 
forall (n_pre: Z) (values: (@list Z)) (counts_2: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : ((Znth i counts_2 0) <> mx)) (PreH2 : ((Znth i counts_2 0) <= mx)) (PreH3 : (i <= n_pre)) (PreH4 : (cnt <> 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH9 : (Pre values )) (PreH10 : (1 <= i)) (PreH11 : (i <= (n_pre + 1 ))) (PreH12 : (0 <= mx)) (PreH13 : (mx <= n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c <= (i - 1 ))) (PreH16 : (CountPrefix values n_pre counts_2 )) (PreH17 : (MaximumFrequencyPrefix counts_2 i mx c )) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts_2 0)) /\ ((Znth k_2 counts_2 0) <= n_pre)))) ,
  (MaximumFrequencyPrefix counts_2 (i + 1 ) mx c )
.

Definition solver_entail_wit_5 := 
(
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (counts_2: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : (i > n_pre)) (PreH2 : (cnt <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= (Zlength (values)))))) (PreH7 : (Pre values )) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1 ))) (PreH10 : (0 <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : (0 <= c)) (PreH13 : (c <= (i - 1 ))) (PreH14 : (CountPrefix values n_pre counts_2 )) (PreH15 : (MaximumFrequencyPrefix counts_2 i mx c )) (PreH16 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= n_pre)) -> ((0 <= (Znth k_3 counts_2 0)) /\ ((Znth k_3 counts_2 0) <= n_pre)))) ,
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full cnt (n_pre + 1 ) counts_2 )
|--
  EX (counts: (@list Z)) ,
  “ (cnt <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (2 <= (Zlength (values))) ” 
  &&  “ ((Zlength (values)) <= 100000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values))))) ” 
  &&  “ (Pre values ) ” 
  &&  “ (2 <= mx) ” 
  &&  “ (mx <= n_pre) ” 
  &&  “ (1 <= c) ” 
  &&  “ (c <= n_pre) ” 
  &&  “ ((((n_pre - c ) ÷ (mx - 1 ) ) - 1 ) = (((n_pre - c ) ÷ (mx - 1 ) ) - 1 )) ” 
  &&  “ (CountPrefix values n_pre counts ) ” 
  &&  “ (MaximumFrequencyPrefix counts (n_pre + 1 ) mx c ) ” 
  &&  “ (Spec values (((n_pre - c ) ÷ (mx - 1 ) ) - 1 ) ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full cnt (n_pre + 1 ) counts )
) \/
(
forall (n_pre: Z) (values: (@list Z)) (counts_2: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : (i > n_pre)) (PreH2 : (cnt <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= (Zlength (values)))))) (PreH7 : (Pre values )) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1 ))) (PreH10 : (0 <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : (0 <= c)) (PreH13 : (c <= (i - 1 ))) (PreH14 : (CountPrefix values n_pre counts_2 )) (PreH15 : (MaximumFrequencyPrefix counts_2 i mx c )) (PreH16 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= n_pre)) -> ((0 <= (Znth k_3 counts_2 0)) /\ ((Znth k_3 counts_2 0) <= n_pre)))) ,
  TT && emp 
|--
  “ (Spec values (((n_pre - c ) ÷ (mx - 1 ) ) - 1 ) ) ” 
  &&  “ (MaximumFrequencyPrefix counts_2 (n_pre + 1 ) mx c ) ” 
  &&  “ (1 <= c) ” 
  &&  “ (2 <= mx) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values))))) ”
  &&  emp
).

Definition solver_entail_wit_5_split_goal_1 := 
forall (n_pre: Z) (values: (@list Z)) (counts_2: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : (i > n_pre)) (PreH2 : (cnt <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= (Zlength (values)))))) (PreH7 : (Pre values )) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1 ))) (PreH10 : (0 <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : (0 <= c)) (PreH13 : (c <= (i - 1 ))) (PreH14 : (CountPrefix values n_pre counts_2 )) (PreH15 : (MaximumFrequencyPrefix counts_2 i mx c )) (PreH16 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= n_pre)) -> ((0 <= (Znth k_3 counts_2 0)) /\ ((Znth k_3 counts_2 0) <= n_pre)))) ,
  (Spec values (((n_pre - c ) ÷ (mx - 1 ) ) - 1 ) )
.

Definition solver_entail_wit_5_split_goal_2 := 
forall (n_pre: Z) (values: (@list Z)) (counts_2: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : (i > n_pre)) (PreH2 : (cnt <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= (Zlength (values)))))) (PreH7 : (Pre values )) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1 ))) (PreH10 : (0 <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : (0 <= c)) (PreH13 : (c <= (i - 1 ))) (PreH14 : (CountPrefix values n_pre counts_2 )) (PreH15 : (MaximumFrequencyPrefix counts_2 i mx c )) (PreH16 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= n_pre)) -> ((0 <= (Znth k_3 counts_2 0)) /\ ((Znth k_3 counts_2 0) <= n_pre)))) ,
  (MaximumFrequencyPrefix counts_2 (n_pre + 1 ) mx c )
.

Definition solver_entail_wit_5_split_goal_3 := 
forall (n_pre: Z) (values: (@list Z)) (counts_2: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : (i > n_pre)) (PreH2 : (cnt <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= (Zlength (values)))))) (PreH7 : (Pre values )) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1 ))) (PreH10 : (0 <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : (0 <= c)) (PreH13 : (c <= (i - 1 ))) (PreH14 : (CountPrefix values n_pre counts_2 )) (PreH15 : (MaximumFrequencyPrefix counts_2 i mx c )) (PreH16 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= n_pre)) -> ((0 <= (Znth k_3 counts_2 0)) /\ ((Znth k_3 counts_2 0) <= n_pre)))) ,
  (1 <= c)
.

Definition solver_entail_wit_5_split_goal_4 := 
forall (n_pre: Z) (values: (@list Z)) (counts_2: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : (i > n_pre)) (PreH2 : (cnt <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= (Zlength (values)))))) (PreH7 : (Pre values )) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1 ))) (PreH10 : (0 <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : (0 <= c)) (PreH13 : (c <= (i - 1 ))) (PreH14 : (CountPrefix values n_pre counts_2 )) (PreH15 : (MaximumFrequencyPrefix counts_2 i mx c )) (PreH16 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= n_pre)) -> ((0 <= (Znth k_3 counts_2 0)) /\ ((Znth k_3 counts_2 0) <= n_pre)))) ,
  (2 <= mx)
.

Definition solver_entail_wit_5_split_goal_5 := 
forall (n_pre: Z) (values: (@list Z)) (counts_2: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : (i > n_pre)) (PreH2 : (cnt <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= (Zlength (values)))))) (PreH7 : (Pre values )) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1 ))) (PreH10 : (0 <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : (0 <= c)) (PreH13 : (c <= (i - 1 ))) (PreH14 : (CountPrefix values n_pre counts_2 )) (PreH15 : (MaximumFrequencyPrefix counts_2 i mx c )) (PreH16 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= n_pre)) -> ((0 <= (Znth k_3 counts_2 0)) /\ ((Znth k_3 counts_2 0) <= n_pre)))) ,
  forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))
.

Definition solver_return_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (counts: (@list Z)) (cnt: Z) (mx: Z) (c: Z) (ans: Z) (PreH1 : (cnt <> 0)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 100000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH6 : (Pre values )) (PreH7 : (2 <= mx)) (PreH8 : (mx <= n_pre)) (PreH9 : (1 <= c)) (PreH10 : (c <= n_pre)) (PreH11 : (ans = (((n_pre - c ) ÷ (mx - 1 ) ) - 1 ))) (PreH12 : (CountPrefix values n_pre counts )) (PreH13 : (MaximumFrequencyPrefix counts (n_pre + 1 ) mx c )) (PreH14 : (Spec values ans )) ,
  (IntArray.full a_pre n_pre values )
|--
  “ (Spec values ans ) ”
  &&  (IntArray.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_1_pure := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (PreH1 : (2 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= (Zlength (values)))))) (PreH4 : (Pre values )) (PreH5 : (n_pre = (Zlength (values)))) ,
  ((( &( "cnt" ) )) # Ptr  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (0 <= (n_pre + 1 )) ” 
  &&  “ ((n_pre + 1 ) = (n_pre + 1 )) ” 
  &&  “ (sizeof(INT) = sizeof(INT)) ”
.

Definition solver_partial_solve_wit_1_aux := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (PreH1 : (2 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= (Zlength (values)))))) (PreH4 : (Pre values )) (PreH5 : (n_pre = (Zlength (values)))) ,
  (IntArray.full a_pre n_pre values )
|--
  “ (0 <= (n_pre + 1 )) ” 
  &&  “ ((n_pre + 1 ) = (n_pre + 1 )) ” 
  &&  “ (sizeof(INT) = sizeof(INT)) ” 
  &&  “ (2 <= (Zlength (values))) ” 
  &&  “ ((Zlength (values)) <= 100000) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= (Zlength (values))))) ” 
  &&  “ (Pre values ) ” 
  &&  “ (n_pre = (Zlength (values))) ”
  &&  (IntArray.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (counts: (@list Z)) (i: Z) (c: Z) (mx: Z) (cnt: Z) (PreH1 : (i < n_pre)) (PreH2 : (cnt <> 0)) (PreH3 : (mx = 0)) (PreH4 : (c = 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH9 : (Pre values )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (CountPrefix values i counts )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= i)))) ,
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full cnt (n_pre + 1 ) counts )
|--
  “ (i < n_pre) ” 
  &&  “ (cnt <> 0) ” 
  &&  “ (mx = 0) ” 
  &&  “ (c = 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (2 <= (Zlength (values))) ” 
  &&  “ ((Zlength (values)) <= 100000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values))))) ” 
  &&  “ (Pre values ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (CountPrefix values i counts ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= i))) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i values 0))
  **  (IntArray.missing_i a_pre i 0 n_pre values )
  **  (IntArray.full cnt (n_pre + 1 ) counts )
.

Definition solver_partial_solve_wit_3 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (counts: (@list Z)) (i: Z) (c: Z) (mx: Z) (cnt: Z) (PreH1 : (i < n_pre)) (PreH2 : (cnt <> 0)) (PreH3 : (mx = 0)) (PreH4 : (c = 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH9 : (Pre values )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (CountPrefix values i counts )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= i)))) ,
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full cnt (n_pre + 1 ) counts )
|--
  “ (i < n_pre) ” 
  &&  “ (cnt <> 0) ” 
  &&  “ (mx = 0) ” 
  &&  “ (c = 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (2 <= (Zlength (values))) ” 
  &&  “ ((Zlength (values)) <= 100000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values))))) ” 
  &&  “ (Pre values ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (CountPrefix values i counts ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= i))) ”
  &&  (((cnt + ((Znth i values 0) * sizeof(INT)))) # Int  |-> (Znth (Znth i values 0) counts 0))
  **  (IntArray.missing_i cnt (Znth i values 0) 0 (n_pre + 1 ) counts )
  **  (IntArray.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_4 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (counts: (@list Z)) (i: Z) (c: Z) (mx: Z) (cnt: Z) (PreH1 : (i < n_pre)) (PreH2 : (cnt <> 0)) (PreH3 : (mx = 0)) (PreH4 : (c = 0)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : (2 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH9 : (Pre values )) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (CountPrefix values i counts )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= i)))) ,
  (IntArray.full cnt (n_pre + 1 ) counts )
  **  (IntArray.full a_pre n_pre values )
|--
  “ (i < n_pre) ” 
  &&  “ (cnt <> 0) ” 
  &&  “ (mx = 0) ” 
  &&  “ (c = 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (2 <= (Zlength (values))) ” 
  &&  “ ((Zlength (values)) <= 100000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values))))) ” 
  &&  “ (Pre values ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (CountPrefix values i counts ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= i))) ”
  &&  (((cnt + ((Znth i values 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i cnt (Znth i values 0) 0 (n_pre + 1 ) counts )
  **  (IntArray.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_5 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (counts: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : (i <= n_pre)) (PreH2 : (cnt <> 0)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH7 : (Pre values )) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1 ))) (PreH10 : (0 <= mx)) (PreH11 : (mx <= n_pre)) (PreH12 : (0 <= c)) (PreH13 : (c <= (i - 1 ))) (PreH14 : (CountPrefix values n_pre counts )) (PreH15 : (MaximumFrequencyPrefix counts i mx c )) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= n_pre)))) ,
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full cnt (n_pre + 1 ) counts )
|--
  “ (i <= n_pre) ” 
  &&  “ (cnt <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (2 <= (Zlength (values))) ” 
  &&  “ ((Zlength (values)) <= 100000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values))))) ” 
  &&  “ (Pre values ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c <= (i - 1 )) ” 
  &&  “ (CountPrefix values n_pre counts ) ” 
  &&  “ (MaximumFrequencyPrefix counts i mx c ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= n_pre))) ”
  &&  (((cnt + (i * sizeof(INT)))) # Int  |-> (Znth i counts 0))
  **  (IntArray.missing_i cnt i 0 (n_pre + 1 ) counts )
  **  (IntArray.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_6 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (counts: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : ((Znth i counts 0) > mx)) (PreH2 : (i <= n_pre)) (PreH3 : (cnt <> 0)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH8 : (Pre values )) (PreH9 : (1 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (0 <= mx)) (PreH12 : (mx <= n_pre)) (PreH13 : (0 <= c)) (PreH14 : (c <= (i - 1 ))) (PreH15 : (CountPrefix values n_pre counts )) (PreH16 : (MaximumFrequencyPrefix counts i mx c )) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= n_pre)))) ,
  (IntArray.full cnt (n_pre + 1 ) counts )
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((Znth i counts 0) > mx) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (cnt <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (2 <= (Zlength (values))) ” 
  &&  “ ((Zlength (values)) <= 100000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values))))) ” 
  &&  “ (Pre values ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c <= (i - 1 )) ” 
  &&  “ (CountPrefix values n_pre counts ) ” 
  &&  “ (MaximumFrequencyPrefix counts i mx c ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= n_pre))) ”
  &&  (((cnt + (i * sizeof(INT)))) # Int  |-> (Znth i counts 0))
  **  (IntArray.missing_i cnt i 0 (n_pre + 1 ) counts )
  **  (IntArray.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_7 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (counts: (@list Z)) (c: Z) (mx: Z) (i: Z) (cnt: Z) (PreH1 : ((Znth i counts 0) <= mx)) (PreH2 : (i <= n_pre)) (PreH3 : (cnt <> 0)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH8 : (Pre values )) (PreH9 : (1 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (0 <= mx)) (PreH12 : (mx <= n_pre)) (PreH13 : (0 <= c)) (PreH14 : (c <= (i - 1 ))) (PreH15 : (CountPrefix values n_pre counts )) (PreH16 : (MaximumFrequencyPrefix counts i mx c )) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= n_pre)))) ,
  (IntArray.full cnt (n_pre + 1 ) counts )
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((Znth i counts 0) <= mx) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (cnt <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (2 <= (Zlength (values))) ” 
  &&  “ ((Zlength (values)) <= 100000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values))))) ” 
  &&  “ (Pre values ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ (0 <= mx) ” 
  &&  “ (mx <= n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c <= (i - 1 )) ” 
  &&  “ (CountPrefix values n_pre counts ) ” 
  &&  “ (MaximumFrequencyPrefix counts i mx c ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 counts 0)) /\ ((Znth k_2 counts 0) <= n_pre))) ”
  &&  (((cnt + (i * sizeof(INT)))) # Int  |-> (Znth i counts 0))
  **  (IntArray.missing_i cnt i 0 (n_pre + 1 ) counts )
  **  (IntArray.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_8 := 
forall (n_pre: Z) (a_pre: Z) (values: (@list Z)) (counts: (@list Z)) (cnt: Z) (mx: Z) (c: Z) (ans: Z) (PreH1 : (cnt <> 0)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 100000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values)))))) (PreH6 : (Pre values )) (PreH7 : (2 <= mx)) (PreH8 : (mx <= n_pre)) (PreH9 : (1 <= c)) (PreH10 : (c <= n_pre)) (PreH11 : (ans = (((n_pre - c ) ÷ (mx - 1 ) ) - 1 ))) (PreH12 : (CountPrefix values n_pre counts )) (PreH13 : (MaximumFrequencyPrefix counts (n_pre + 1 ) mx c )) (PreH14 : (Spec values ans )) ,
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full cnt (n_pre + 1 ) counts )
|--
  “ (cnt <> 0) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ (2 <= (Zlength (values))) ” 
  &&  “ ((Zlength (values)) <= 100000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= (Zlength (values))))) ” 
  &&  “ (Pre values ) ” 
  &&  “ (2 <= mx) ” 
  &&  “ (mx <= n_pre) ” 
  &&  “ (1 <= c) ” 
  &&  “ (c <= n_pre) ” 
  &&  “ (ans = (((n_pre - c ) ÷ (mx - 1 ) ) - 1 )) ” 
  &&  “ (CountPrefix values n_pre counts ) ” 
  &&  “ (MaximumFrequencyPrefix counts (n_pre + 1 ) mx c ) ” 
  &&  “ (Spec values ans ) ”
  &&  (IntArray.full cnt ((Zlength (values)) + 1 ) counts )
  **  (IntArray.full a_pre n_pre values )
.

Module Type VC_Correct.


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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Axiom proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Axiom proof_of_solver_entail_wit_4_3 : solver_entail_wit_4_3.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.
Axiom proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8.

End VC_Correct.
