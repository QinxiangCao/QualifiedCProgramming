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
Require Import AUXLib.MonotonicList.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P043_649C_pechat_uslovii_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (l1: (@list Z)) (PreH1 : (Permutation page_counts l1 )) (PreH2 : (mono_nondec l1 )) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre >= 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i page_counts 0)) /\ ((Znth i page_counts 0) <= 10000)))) (PreH8 : (n_pre = (Zlength (page_counts)))) ,
  ((( &( "served" ) )) # Int  |->_)
  **  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (l1: (@list Z)) (PreH1 : (Permutation page_counts l1 )) (PreH2 : (mono_nondec l1 )) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre >= 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i page_counts 0)) /\ ((Znth i page_counts 0) <= 10000)))) (PreH8 : (n_pre = (Zlength (page_counts)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "served" ) )) # Int  |-> 0)
  **  (IntArray.full a_pre n_pre l1 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (sorted_pages)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (served = i)) (PreH8 : (0 <= x)) (PreH9 : (x <= x_pre)) (PreH10 : (0 <= y)) (PreH11 : (y <= y_pre)) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH13 : (Permutation page_counts sorted_pages )) (PreH14 : (mono_nondec sorted_pages )) (PreH15 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |->_)
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> (Znth i sorted_pages 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ (((Znth i sorted_pages 0) <> (INT64_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition solver_safety_wit_4 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (sorted_pages)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (served = i)) (PreH8 : (0 <= x)) (PreH9 : (x <= x_pre)) (PreH10 : (0 <= y)) (PreH11 : (y <= y_pre)) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH13 : (Permutation page_counts sorted_pages )) (PreH14 : (mono_nondec sorted_pages )) (PreH15 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |->_)
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> (Znth i sorted_pages 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_5 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) ÷ 2 ) > x)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted_pages)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (served = i)) (PreH9 : (0 <= x)) (PreH10 : (x <= x_pre)) (PreH11 : (0 <= y)) (PreH12 : (y <= y_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH14 : (Permutation page_counts sorted_pages )) (PreH15 : (mono_nondec sorted_pages )) (PreH16 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> x)
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> (Znth i sorted_pages 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ ((x - x ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (x - x )) ”
.

Definition solver_safety_wit_6 := 
(
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) ÷ 2 ) <= x)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted_pages)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (served = i)) (PreH9 : (0 <= x)) (PreH10 : (x <= x_pre)) (PreH11 : (0 <= y)) (PreH12 : (y <= y_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH14 : (Permutation page_counts sorted_pages )) (PreH15 : (mono_nondec sorted_pages )) (PreH16 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> ((Znth i sorted_pages 0) ÷ 2 ))
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> (Znth i sorted_pages 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ ((x - ((Znth i sorted_pages 0) ÷ 2 ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (x - ((Znth i sorted_pages 0) ÷ 2 ) )) ”
) \/
(
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) ÷ 2 ) <= x)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted_pages)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (served = i)) (PreH9 : (0 <= x)) (PreH10 : (x <= x_pre)) (PreH11 : (0 <= y)) (PreH12 : (y <= y_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH14 : (Permutation page_counts sorted_pages )) (PreH15 : (mono_nondec sorted_pages )) (PreH16 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> ((Znth i sorted_pages 0) ÷ 2 ))
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> (Znth i sorted_pages 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ ((x - ((Znth i sorted_pages 0) ÷ 2 ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (x - ((Znth i sorted_pages 0) ÷ 2 ) )) ”
).

Definition solver_safety_wit_6_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) ÷ 2 ) <= x)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted_pages)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (served = i)) (PreH9 : (0 <= x)) (PreH10 : (x <= x_pre)) (PreH11 : (0 <= y)) (PreH12 : (y <= y_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH14 : (Permutation page_counts sorted_pages )) (PreH15 : (mono_nondec sorted_pages )) (PreH16 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> ((Znth i sorted_pages 0) ÷ 2 ))
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> (Znth i sorted_pages 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ ((x - ((Znth i sorted_pages 0) ÷ 2 ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_6_split_goal_2 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) ÷ 2 ) <= x)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted_pages)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (served = i)) (PreH9 : (0 <= x)) (PreH10 : (x <= x_pre)) (PreH11 : (0 <= y)) (PreH12 : (y <= y_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH14 : (Permutation page_counts sorted_pages )) (PreH15 : (mono_nondec sorted_pages )) (PreH16 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> ((Znth i sorted_pages 0) ÷ 2 ))
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> (Znth i sorted_pages 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> x)
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ ((INT64_MIN) <= (x - ((Znth i sorted_pages 0) ÷ 2 ) )) ”
.

Definition solver_safety_wit_7 := 
(
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) ÷ 2 ) > x)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted_pages)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (served = i)) (PreH9 : (0 <= x)) (PreH10 : (x <= x_pre)) (PreH11 : (0 <= y)) (PreH12 : (y <= y_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH14 : (Permutation page_counts sorted_pages )) (PreH15 : (mono_nondec sorted_pages )) (PreH16 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> x)
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> (Znth i sorted_pages 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> (x - x ))
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ (((Znth i sorted_pages 0) - (2 * x ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth i sorted_pages 0) - (2 * x ) )) ”
) \/
(
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) ÷ 2 ) > x)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted_pages)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (served = i)) (PreH9 : (0 <= x)) (PreH10 : (x <= x_pre)) (PreH11 : (0 <= y)) (PreH12 : (y <= y_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH14 : (Permutation page_counts sorted_pages )) (PreH15 : (mono_nondec sorted_pages )) (PreH16 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> x)
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> (Znth i sorted_pages 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> (x - x ))
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ (((Znth i sorted_pages 0) - (2 * x ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth i sorted_pages 0) - (2 * x ) )) ”
).

Definition solver_safety_wit_7_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) ÷ 2 ) > x)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted_pages)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (served = i)) (PreH9 : (0 <= x)) (PreH10 : (x <= x_pre)) (PreH11 : (0 <= y)) (PreH12 : (y <= y_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH14 : (Permutation page_counts sorted_pages )) (PreH15 : (mono_nondec sorted_pages )) (PreH16 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> x)
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> (Znth i sorted_pages 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> (x - x ))
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ (((Znth i sorted_pages 0) - (2 * x ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_7_split_goal_2 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) ÷ 2 ) > x)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted_pages)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (served = i)) (PreH9 : (0 <= x)) (PreH10 : (x <= x_pre)) (PreH11 : (0 <= y)) (PreH12 : (y <= y_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH14 : (Permutation page_counts sorted_pages )) (PreH15 : (mono_nondec sorted_pages )) (PreH16 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> x)
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> (Znth i sorted_pages 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> (x - x ))
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ ((INT64_MIN) <= ((Znth i sorted_pages 0) - (2 * x ) )) ”
.

Definition solver_safety_wit_8 := 
(
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) ÷ 2 ) > x)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted_pages)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (served = i)) (PreH9 : (0 <= x)) (PreH10 : (x <= x_pre)) (PreH11 : (0 <= y)) (PreH12 : (y <= y_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH14 : (Permutation page_counts sorted_pages )) (PreH15 : (mono_nondec sorted_pages )) (PreH16 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> x)
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> (Znth i sorted_pages 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> (x - x ))
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ ((2 * x ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (2 * x )) ”
) \/
(
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) ÷ 2 ) > x)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted_pages)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (served = i)) (PreH9 : (0 <= x)) (PreH10 : (x <= x_pre)) (PreH11 : (0 <= y)) (PreH12 : (y <= y_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH14 : (Permutation page_counts sorted_pages )) (PreH15 : (mono_nondec sorted_pages )) (PreH16 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> x)
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> (Znth i sorted_pages 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> (x - x ))
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ ((2 * x ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (2 * x )) ”
).

Definition solver_safety_wit_8_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) ÷ 2 ) > x)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted_pages)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (served = i)) (PreH9 : (0 <= x)) (PreH10 : (x <= x_pre)) (PreH11 : (0 <= y)) (PreH12 : (y <= y_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH14 : (Permutation page_counts sorted_pages )) (PreH15 : (mono_nondec sorted_pages )) (PreH16 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> x)
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> (Znth i sorted_pages 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> (x - x ))
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ ((2 * x ) <= INT64_MAX) ”
.

Definition solver_safety_wit_8_split_goal_2 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) ÷ 2 ) > x)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted_pages)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (served = i)) (PreH9 : (0 <= x)) (PreH10 : (x <= x_pre)) (PreH11 : (0 <= y)) (PreH12 : (y <= y_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH14 : (Permutation page_counts sorted_pages )) (PreH15 : (mono_nondec sorted_pages )) (PreH16 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> x)
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> (Znth i sorted_pages 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> (x - x ))
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ ((INT64_MIN) <= (2 * x )) ”
.

Definition solver_safety_wit_9 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) ÷ 2 ) > x)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted_pages)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (served = i)) (PreH9 : (0 <= x)) (PreH10 : (x <= x_pre)) (PreH11 : (0 <= y)) (PreH12 : (y <= y_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH14 : (Permutation page_counts sorted_pages )) (PreH15 : (mono_nondec sorted_pages )) (PreH16 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> x)
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> (Znth i sorted_pages 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> (x - x ))
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_10 := 
(
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) ÷ 2 ) <= x)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted_pages)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (served = i)) (PreH9 : (0 <= x)) (PreH10 : (x <= x_pre)) (PreH11 : (0 <= y)) (PreH12 : (y <= y_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH14 : (Permutation page_counts sorted_pages )) (PreH15 : (mono_nondec sorted_pages )) (PreH16 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> ((Znth i sorted_pages 0) ÷ 2 ))
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> (Znth i sorted_pages 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> (x - ((Znth i sorted_pages 0) ÷ 2 ) ))
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ (((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) )) ”
) \/
(
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) ÷ 2 ) <= x)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted_pages)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (served = i)) (PreH9 : (0 <= x)) (PreH10 : (x <= x_pre)) (PreH11 : (0 <= y)) (PreH12 : (y <= y_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH14 : (Permutation page_counts sorted_pages )) (PreH15 : (mono_nondec sorted_pages )) (PreH16 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> ((Znth i sorted_pages 0) ÷ 2 ))
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> (Znth i sorted_pages 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> (x - ((Znth i sorted_pages 0) ÷ 2 ) ))
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ (((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) )) ”
).

Definition solver_safety_wit_10_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) ÷ 2 ) <= x)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted_pages)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (served = i)) (PreH9 : (0 <= x)) (PreH10 : (x <= x_pre)) (PreH11 : (0 <= y)) (PreH12 : (y <= y_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH14 : (Permutation page_counts sorted_pages )) (PreH15 : (mono_nondec sorted_pages )) (PreH16 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> ((Znth i sorted_pages 0) ÷ 2 ))
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> (Znth i sorted_pages 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> (x - ((Znth i sorted_pages 0) ÷ 2 ) ))
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ (((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_10_split_goal_2 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) ÷ 2 ) <= x)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted_pages)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (served = i)) (PreH9 : (0 <= x)) (PreH10 : (x <= x_pre)) (PreH11 : (0 <= y)) (PreH12 : (y <= y_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH14 : (Permutation page_counts sorted_pages )) (PreH15 : (mono_nondec sorted_pages )) (PreH16 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> ((Znth i sorted_pages 0) ÷ 2 ))
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> (Znth i sorted_pages 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> (x - ((Znth i sorted_pages 0) ÷ 2 ) ))
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ ((INT64_MIN) <= ((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) )) ”
.

Definition solver_safety_wit_11 := 
(
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) ÷ 2 ) <= x)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted_pages)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (served = i)) (PreH9 : (0 <= x)) (PreH10 : (x <= x_pre)) (PreH11 : (0 <= y)) (PreH12 : (y <= y_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH14 : (Permutation page_counts sorted_pages )) (PreH15 : (mono_nondec sorted_pages )) (PreH16 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> ((Znth i sorted_pages 0) ÷ 2 ))
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> (Znth i sorted_pages 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> (x - ((Znth i sorted_pages 0) ÷ 2 ) ))
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ ((2 * ((Znth i sorted_pages 0) ÷ 2 ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (2 * ((Znth i sorted_pages 0) ÷ 2 ) )) ”
) \/
(
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) ÷ 2 ) <= x)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted_pages)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (served = i)) (PreH9 : (0 <= x)) (PreH10 : (x <= x_pre)) (PreH11 : (0 <= y)) (PreH12 : (y <= y_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH14 : (Permutation page_counts sorted_pages )) (PreH15 : (mono_nondec sorted_pages )) (PreH16 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> ((Znth i sorted_pages 0) ÷ 2 ))
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> (Znth i sorted_pages 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> (x - ((Znth i sorted_pages 0) ÷ 2 ) ))
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ ((2 * ((Znth i sorted_pages 0) ÷ 2 ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (2 * ((Znth i sorted_pages 0) ÷ 2 ) )) ”
).

Definition solver_safety_wit_11_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) ÷ 2 ) <= x)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted_pages)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (served = i)) (PreH9 : (0 <= x)) (PreH10 : (x <= x_pre)) (PreH11 : (0 <= y)) (PreH12 : (y <= y_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH14 : (Permutation page_counts sorted_pages )) (PreH15 : (mono_nondec sorted_pages )) (PreH16 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> ((Znth i sorted_pages 0) ÷ 2 ))
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> (Znth i sorted_pages 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> (x - ((Znth i sorted_pages 0) ÷ 2 ) ))
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ ((2 * ((Znth i sorted_pages 0) ÷ 2 ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_11_split_goal_2 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) ÷ 2 ) <= x)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted_pages)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (served = i)) (PreH9 : (0 <= x)) (PreH10 : (x <= x_pre)) (PreH11 : (0 <= y)) (PreH12 : (y <= y_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH14 : (Permutation page_counts sorted_pages )) (PreH15 : (mono_nondec sorted_pages )) (PreH16 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> ((Znth i sorted_pages 0) ÷ 2 ))
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> (Znth i sorted_pages 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> (x - ((Znth i sorted_pages 0) ÷ 2 ) ))
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ ((INT64_MIN) <= (2 * ((Znth i sorted_pages 0) ÷ 2 ) )) ”
.

Definition solver_safety_wit_12 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) ÷ 2 ) <= x)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted_pages)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (served = i)) (PreH9 : (0 <= x)) (PreH10 : (x <= x_pre)) (PreH11 : (0 <= y)) (PreH12 : (y <= y_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH14 : (Permutation page_counts sorted_pages )) (PreH15 : (mono_nondec sorted_pages )) (PreH16 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> ((Znth i sorted_pages 0) ÷ 2 ))
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> (Znth i sorted_pages 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> (x - ((Znth i sorted_pages 0) ÷ 2 ) ))
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_13 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) ÷ 2 ) > x)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted_pages)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (served = i)) (PreH9 : (0 <= x)) (PreH10 : (x <= x_pre)) (PreH11 : (0 <= y)) (PreH12 : (y <= y_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH14 : (Permutation page_counts sorted_pages )) (PreH15 : (mono_nondec sorted_pages )) (PreH16 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> x)
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> ((Znth i sorted_pages 0) - (2 * x ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> (x - x ))
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_14 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) ÷ 2 ) <= x)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted_pages)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (served = i)) (PreH9 : (0 <= x)) (PreH10 : (x <= x_pre)) (PreH11 : (0 <= y)) (PreH12 : (y <= y_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH14 : (Permutation page_counts sorted_pages )) (PreH15 : (mono_nondec sorted_pages )) (PreH16 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> ((Znth i sorted_pages 0) ÷ 2 ))
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> ((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> (x - ((Znth i sorted_pages 0) ÷ 2 ) ))
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_15 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) - (2 * x ) ) <= y)) (PreH2 : (((Znth i sorted_pages 0) - (2 * x ) ) > 0)) (PreH3 : (((Znth i sorted_pages 0) ÷ 2 ) > x)) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : ((Zlength (sorted_pages)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (served = i)) (PreH11 : (0 <= x)) (PreH12 : (x <= x_pre)) (PreH13 : (0 <= y)) (PreH14 : (y <= y_pre)) (PreH15 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH16 : (Permutation page_counts sorted_pages )) (PreH17 : (mono_nondec sorted_pages )) (PreH18 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> x)
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> ((Znth i sorted_pages 0) - (2 * x ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> (x - x ))
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ ((y - ((Znth i sorted_pages 0) - (2 * x ) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (y - ((Znth i sorted_pages 0) - (2 * x ) ) )) ”
.

Definition solver_safety_wit_16 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ) <= y)) (PreH2 : (((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ) > 0)) (PreH3 : (((Znth i sorted_pages 0) ÷ 2 ) <= x)) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : ((Zlength (sorted_pages)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (served = i)) (PreH11 : (0 <= x)) (PreH12 : (x <= x_pre)) (PreH13 : (0 <= y)) (PreH14 : (y <= y_pre)) (PreH15 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH16 : (Permutation page_counts sorted_pages )) (PreH17 : (mono_nondec sorted_pages )) (PreH18 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> ((Znth i sorted_pages 0) ÷ 2 ))
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> ((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> (x - ((Znth i sorted_pages 0) ÷ 2 ) ))
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ ((y - ((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (y - ((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ) )) ”
.

Definition solver_safety_wit_17 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) - (2 * x ) ) > y)) (PreH2 : (((Znth i sorted_pages 0) - (2 * x ) ) > 0)) (PreH3 : (((Znth i sorted_pages 0) ÷ 2 ) > x)) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : ((Zlength (sorted_pages)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (served = i)) (PreH11 : (0 <= x)) (PreH12 : (x <= x_pre)) (PreH13 : (0 <= y)) (PreH14 : (y <= y_pre)) (PreH15 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH16 : (Permutation page_counts sorted_pages )) (PreH17 : (mono_nondec sorted_pages )) (PreH18 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> x)
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> ((Znth i sorted_pages 0) - (2 * x ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> (x - x ))
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_18 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ) > y)) (PreH2 : (((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ) > 0)) (PreH3 : (((Znth i sorted_pages 0) ÷ 2 ) <= x)) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : ((Zlength (sorted_pages)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (served = i)) (PreH11 : (0 <= x)) (PreH12 : (x <= x_pre)) (PreH13 : (0 <= y)) (PreH14 : (y <= y_pre)) (PreH15 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH16 : (Permutation page_counts sorted_pages )) (PreH17 : (mono_nondec sorted_pages )) (PreH18 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> ((Znth i sorted_pages 0) ÷ 2 ))
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> ((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> (x - ((Znth i sorted_pages 0) ÷ 2 ) ))
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_19 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ) = 1)) (PreH2 : (((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ) > y)) (PreH3 : (((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ) > 0)) (PreH4 : (((Znth i sorted_pages 0) ÷ 2 ) <= x)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : ((Zlength (sorted_pages)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (served = i)) (PreH12 : (0 <= x)) (PreH13 : (x <= x_pre)) (PreH14 : (0 <= y)) (PreH15 : (y <= y_pre)) (PreH16 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH17 : (Permutation page_counts sorted_pages )) (PreH18 : (mono_nondec sorted_pages )) (PreH19 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> ((Znth i sorted_pages 0) ÷ 2 ))
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> ((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> (x - ((Znth i sorted_pages 0) ÷ 2 ) ))
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_20 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) - (2 * x ) ) = 1)) (PreH2 : (((Znth i sorted_pages 0) - (2 * x ) ) > y)) (PreH3 : (((Znth i sorted_pages 0) - (2 * x ) ) > 0)) (PreH4 : (((Znth i sorted_pages 0) ÷ 2 ) > x)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : ((Zlength (sorted_pages)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (served = i)) (PreH12 : (0 <= x)) (PreH13 : (x <= x_pre)) (PreH14 : (0 <= y)) (PreH15 : (y <= y_pre)) (PreH16 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH17 : (Permutation page_counts sorted_pages )) (PreH18 : (mono_nondec sorted_pages )) (PreH19 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> x)
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> ((Znth i sorted_pages 0) - (2 * x ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> (x - x ))
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_21 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : ((x - x ) > 0)) (PreH2 : (((Znth i sorted_pages 0) - (2 * x ) ) = 1)) (PreH3 : (((Znth i sorted_pages 0) - (2 * x ) ) > y)) (PreH4 : (((Znth i sorted_pages 0) - (2 * x ) ) > 0)) (PreH5 : (((Znth i sorted_pages 0) ÷ 2 ) > x)) (PreH6 : (i < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((Zlength (sorted_pages)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (served = i)) (PreH13 : (0 <= x)) (PreH14 : (x <= x_pre)) (PreH15 : (0 <= y)) (PreH16 : (y <= y_pre)) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH18 : (Permutation page_counts sorted_pages )) (PreH19 : (mono_nondec sorted_pages )) (PreH20 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> x)
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> ((Znth i sorted_pages 0) - (2 * x ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> (x - x ))
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ False ”
.

Definition solver_safety_wit_22 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : ((x - ((Znth i sorted_pages 0) ÷ 2 ) ) > 0)) (PreH2 : (((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ) = 1)) (PreH3 : (((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ) > y)) (PreH4 : (((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ) > 0)) (PreH5 : (((Znth i sorted_pages 0) ÷ 2 ) <= x)) (PreH6 : (i < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((Zlength (sorted_pages)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (served = i)) (PreH13 : (0 <= x)) (PreH14 : (x <= x_pre)) (PreH15 : (0 <= y)) (PreH16 : (y <= y_pre)) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH18 : (Permutation page_counts sorted_pages )) (PreH19 : (mono_nondec sorted_pages )) (PreH20 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> ((Znth i sorted_pages 0) ÷ 2 ))
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> ((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> (x - ((Znth i sorted_pages 0) ÷ 2 ) ))
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ (((x - ((Znth i sorted_pages 0) ÷ 2 ) ) - 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((x - ((Znth i sorted_pages 0) ÷ 2 ) ) - 1 )) ”
.

Definition solver_safety_wit_23 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) - (2 * x ) ) <= y)) (PreH2 : (((Znth i sorted_pages 0) - (2 * x ) ) > 0)) (PreH3 : (((Znth i sorted_pages 0) ÷ 2 ) > x)) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : ((Zlength (sorted_pages)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (served = i)) (PreH11 : (0 <= x)) (PreH12 : (x <= x_pre)) (PreH13 : (0 <= y)) (PreH14 : (y <= y_pre)) (PreH15 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH16 : (Permutation page_counts sorted_pages )) (PreH17 : (mono_nondec sorted_pages )) (PreH18 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> x)
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> ((Znth i sorted_pages 0) - (2 * x ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> (x - x ))
  **  ((( &( "y" ) )) # Int64  |-> (y - ((Znth i sorted_pages 0) - (2 * x ) ) ))
|--
  “ ((served + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (served + 1 )) ”
.

Definition solver_safety_wit_24 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ) <= y)) (PreH2 : (((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ) > 0)) (PreH3 : (((Znth i sorted_pages 0) ÷ 2 ) <= x)) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : ((Zlength (sorted_pages)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (served = i)) (PreH11 : (0 <= x)) (PreH12 : (x <= x_pre)) (PreH13 : (0 <= y)) (PreH14 : (y <= y_pre)) (PreH15 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH16 : (Permutation page_counts sorted_pages )) (PreH17 : (mono_nondec sorted_pages )) (PreH18 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> ((Znth i sorted_pages 0) ÷ 2 ))
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> ((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> (x - ((Znth i sorted_pages 0) ÷ 2 ) ))
  **  ((( &( "y" ) )) # Int64  |-> (y - ((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ) ))
|--
  “ ((served + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (served + 1 )) ”
.

Definition solver_safety_wit_25 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : ((x - ((Znth i sorted_pages 0) ÷ 2 ) ) > 0)) (PreH2 : (((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ) = 1)) (PreH3 : (((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ) > y)) (PreH4 : (((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ) > 0)) (PreH5 : (((Znth i sorted_pages 0) ÷ 2 ) <= x)) (PreH6 : (i < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((Zlength (sorted_pages)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (served = i)) (PreH13 : (0 <= x)) (PreH14 : (x <= x_pre)) (PreH15 : (0 <= y)) (PreH16 : (y <= y_pre)) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH18 : (Permutation page_counts sorted_pages )) (PreH19 : (mono_nondec sorted_pages )) (PreH20 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> ((Znth i sorted_pages 0) ÷ 2 ))
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> ((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> ((x - ((Znth i sorted_pages 0) ÷ 2 ) ) - 1 ))
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ ((served + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (served + 1 )) ”
.

Definition solver_safety_wit_26 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) - (2 * x ) ) <= 0)) (PreH2 : (((Znth i sorted_pages 0) ÷ 2 ) > x)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted_pages)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (served = i)) (PreH10 : (0 <= x)) (PreH11 : (x <= x_pre)) (PreH12 : (0 <= y)) (PreH13 : (y <= y_pre)) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH15 : (Permutation page_counts sorted_pages )) (PreH16 : (mono_nondec sorted_pages )) (PreH17 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> x)
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> ((Znth i sorted_pages 0) - (2 * x ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> (x - x ))
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ ((served + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (served + 1 )) ”
.

Definition solver_safety_wit_27 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ) <= 0)) (PreH2 : (((Znth i sorted_pages 0) ÷ 2 ) <= x)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted_pages)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (served = i)) (PreH10 : (0 <= x)) (PreH11 : (x <= x_pre)) (PreH12 : (0 <= y)) (PreH13 : (y <= y_pre)) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH15 : (Permutation page_counts sorted_pages )) (PreH16 : (mono_nondec sorted_pages )) (PreH17 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  ((( &( "use" ) )) # Int64  |-> ((Znth i sorted_pages 0) ÷ 2 ))
  **  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "pages" ) )) # Int64  |-> ((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> served)
  **  ((( &( "x" ) )) # Int64  |-> (x - ((Znth i sorted_pages 0) ÷ 2 ) ))
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ ((served + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (served + 1 )) ”
.

Definition solver_safety_wit_28 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) - (2 * x ) ) <= y)) (PreH2 : (((Znth i sorted_pages 0) - (2 * x ) ) > 0)) (PreH3 : (((Znth i sorted_pages 0) ÷ 2 ) > x)) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : ((Zlength (sorted_pages)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (served = i)) (PreH11 : (0 <= x)) (PreH12 : (x <= x_pre)) (PreH13 : (0 <= y)) (PreH14 : (y <= y_pre)) (PreH15 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH16 : (Permutation page_counts sorted_pages )) (PreH17 : (mono_nondec sorted_pages )) (PreH18 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> (served + 1 ))
  **  ((( &( "x" ) )) # Int64  |-> (x - x ))
  **  ((( &( "y" ) )) # Int64  |-> (y - ((Znth i sorted_pages 0) - (2 * x ) ) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_29 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ) <= y)) (PreH2 : (((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ) > 0)) (PreH3 : (((Znth i sorted_pages 0) ÷ 2 ) <= x)) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : ((Zlength (sorted_pages)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (served = i)) (PreH11 : (0 <= x)) (PreH12 : (x <= x_pre)) (PreH13 : (0 <= y)) (PreH14 : (y <= y_pre)) (PreH15 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH16 : (Permutation page_counts sorted_pages )) (PreH17 : (mono_nondec sorted_pages )) (PreH18 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> (served + 1 ))
  **  ((( &( "x" ) )) # Int64  |-> (x - ((Znth i sorted_pages 0) ÷ 2 ) ))
  **  ((( &( "y" ) )) # Int64  |-> (y - ((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_30 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : ((x - ((Znth i sorted_pages 0) ÷ 2 ) ) > 0)) (PreH2 : (((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ) = 1)) (PreH3 : (((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ) > y)) (PreH4 : (((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ) > 0)) (PreH5 : (((Znth i sorted_pages 0) ÷ 2 ) <= x)) (PreH6 : (i < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((Zlength (sorted_pages)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (served = i)) (PreH13 : (0 <= x)) (PreH14 : (x <= x_pre)) (PreH15 : (0 <= y)) (PreH16 : (y <= y_pre)) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH18 : (Permutation page_counts sorted_pages )) (PreH19 : (mono_nondec sorted_pages )) (PreH20 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> (served + 1 ))
  **  ((( &( "x" ) )) # Int64  |-> ((x - ((Znth i sorted_pages 0) ÷ 2 ) ) - 1 ))
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_31 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) - (2 * x ) ) <= 0)) (PreH2 : (((Znth i sorted_pages 0) ÷ 2 ) > x)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted_pages)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (served = i)) (PreH10 : (0 <= x)) (PreH11 : (x <= x_pre)) (PreH12 : (0 <= y)) (PreH13 : (y <= y_pre)) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH15 : (Permutation page_counts sorted_pages )) (PreH16 : (mono_nondec sorted_pages )) (PreH17 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> (served + 1 ))
  **  ((( &( "x" ) )) # Int64  |-> (x - x ))
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_32 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (((Znth i sorted_pages 0) - (2 * ((Znth i sorted_pages 0) ÷ 2 ) ) ) <= 0)) (PreH2 : (((Znth i sorted_pages 0) ÷ 2 ) <= x)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted_pages)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (served = i)) (PreH10 : (0 <= x)) (PreH11 : (x <= x_pre)) (PreH12 : (0 <= y)) (PreH13 : (y <= y_pre)) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH15 : (Permutation page_counts sorted_pages )) (PreH16 : (mono_nondec sorted_pages )) (PreH17 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  (IntArray.full a_pre n_pre sorted_pages )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "served" ) )) # Int  |-> (served + 1 ))
  **  ((( &( "x" ) )) # Int64  |-> (x - ((Znth i sorted_pages 0) ÷ 2 ) ))
  **  ((( &( "y" ) )) # Int64  |-> y)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (l1: (@list Z)) (PreH1 : (Permutation page_counts l1 )) (PreH2 : (mono_nondec l1 )) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre >= 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i page_counts 0)) /\ ((Znth i page_counts 0) <= 10000)))) (PreH8 : (n_pre = (Zlength (page_counts)))) ,
  (IntArray.full a_pre n_pre l1 )
|--
  EX (sorted_pages: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (sorted_pages)) = n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= x_pre) ” 
  &&  “ (0 <= y_pre) ” 
  &&  “ (y_pre <= y_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000))) ” 
  &&  “ (Permutation page_counts sorted_pages ) ” 
  &&  “ (mono_nondec sorted_pages ) ” 
  &&  “ (PrefixResourceState sorted_pages x_pre y_pre 0 x_pre y_pre ) ”
  &&  (IntArray.full a_pre n_pre sorted_pages )
) \/
(
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (page_counts: (@list Z)) (l1: (@list Z)) (PreH1 : (Permutation page_counts l1 )) (PreH2 : (mono_nondec l1 )) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre >= 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i page_counts 0)) /\ ((Znth i page_counts 0) <= 10000)))) (PreH8 : (n_pre = (Zlength (page_counts)))) ,
  TT && emp 
|--
  “ (PrefixResourceState l1 x_pre y_pre 0 x_pre y_pre ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j l1 0)) /\ ((Znth j l1 0) <= 10000))) ” 
  &&  “ ((Zlength (l1)) = n_pre) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (page_counts: (@list Z)) (l1: (@list Z)) (PreH1 : (Permutation page_counts l1 )) (PreH2 : (mono_nondec l1 )) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre >= 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i page_counts 0)) /\ ((Znth i page_counts 0) <= 10000)))) (PreH8 : (n_pre = (Zlength (page_counts)))) ,
  (PrefixResourceState l1 x_pre y_pre 0 x_pre y_pre )
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (page_counts: (@list Z)) (l1: (@list Z)) (PreH1 : (Permutation page_counts l1 )) (PreH2 : (mono_nondec l1 )) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre >= 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i page_counts 0)) /\ ((Znth i page_counts 0) <= 10000)))) (PreH8 : (n_pre = (Zlength (page_counts)))) ,
  forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j l1 0)) /\ ((Znth j l1 0) <= 10000)))
.

Definition solver_entail_wit_1_split_goal_3 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (page_counts: (@list Z)) (l1: (@list Z)) (PreH1 : (Permutation page_counts l1 )) (PreH2 : (mono_nondec l1 )) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre >= 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i page_counts 0)) /\ ((Znth i page_counts 0) <= 10000)))) (PreH8 : (n_pre = (Zlength (page_counts)))) ,
  ((Zlength (l1)) = n_pre)
.

Definition solver_entail_wit_2_1 := 
(
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages_2: (@list Z)) (PreH1 : (((Znth i sorted_pages_2 0) - (2 * x ) ) <= y)) (PreH2 : (((Znth i sorted_pages_2 0) - (2 * x ) ) > 0)) (PreH3 : (((Znth i sorted_pages_2 0) ÷ 2 ) > x)) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : ((Zlength (sorted_pages_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (served = i)) (PreH11 : (0 <= x)) (PreH12 : (x <= x_pre)) (PreH13 : (0 <= y)) (PreH14 : (y <= y_pre)) (PreH15 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages_2 0)) /\ ((Znth j sorted_pages_2 0) <= 10000)))) (PreH16 : (Permutation page_counts sorted_pages_2 )) (PreH17 : (mono_nondec sorted_pages_2 )) (PreH18 : (PrefixResourceState sorted_pages_2 x_pre y_pre i x y )) ,
  (IntArray.full a_pre n_pre sorted_pages_2 )
|--
  EX (sorted_pages: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (sorted_pages)) = n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((served + 1 ) = (i + 1 )) ” 
  &&  “ (0 <= (x - x )) ” 
  &&  “ ((x - x ) <= x_pre) ” 
  &&  “ (0 <= (y - ((Znth i sorted_pages_2 0) - (2 * x ) ) )) ” 
  &&  “ ((y - ((Znth i sorted_pages_2 0) - (2 * x ) ) ) <= y_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000))) ” 
  &&  “ (Permutation page_counts sorted_pages ) ” 
  &&  “ (mono_nondec sorted_pages ) ” 
  &&  “ (PrefixResourceState sorted_pages x_pre y_pre (i + 1 ) (x - x ) (y - ((Znth i sorted_pages_2 0) - (2 * x ) ) ) ) ”
  &&  (IntArray.full a_pre n_pre sorted_pages )
) \/
(
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages_2: (@list Z)) (PreH1 : (((Znth i sorted_pages_2 0) - (2 * x ) ) <= y)) (PreH2 : (((Znth i sorted_pages_2 0) - (2 * x ) ) > 0)) (PreH3 : (((Znth i sorted_pages_2 0) ÷ 2 ) > x)) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : ((Zlength (sorted_pages_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (served = i)) (PreH11 : (0 <= x)) (PreH12 : (x <= x_pre)) (PreH13 : (0 <= y)) (PreH14 : (y <= y_pre)) (PreH15 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages_2 0)) /\ ((Znth j sorted_pages_2 0) <= 10000)))) (PreH16 : (Permutation page_counts sorted_pages_2 )) (PreH17 : (mono_nondec sorted_pages_2 )) (PreH18 : (PrefixResourceState sorted_pages_2 x_pre y_pre i x y )) ,
  TT && emp 
|--
  “ (PrefixResourceState sorted_pages_2 x_pre y_pre (served + 1 ) (x - x ) (y - ((Znth served sorted_pages_2 0) - (2 * x ) ) ) ) ”
  &&  emp
).

Definition solver_entail_wit_2_1_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages_2: (@list Z)) (PreH1 : (((Znth i sorted_pages_2 0) - (2 * x ) ) <= y)) (PreH2 : (((Znth i sorted_pages_2 0) - (2 * x ) ) > 0)) (PreH3 : (((Znth i sorted_pages_2 0) ÷ 2 ) > x)) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : ((Zlength (sorted_pages_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (served = i)) (PreH11 : (0 <= x)) (PreH12 : (x <= x_pre)) (PreH13 : (0 <= y)) (PreH14 : (y <= y_pre)) (PreH15 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages_2 0)) /\ ((Znth j sorted_pages_2 0) <= 10000)))) (PreH16 : (Permutation page_counts sorted_pages_2 )) (PreH17 : (mono_nondec sorted_pages_2 )) (PreH18 : (PrefixResourceState sorted_pages_2 x_pre y_pre i x y )) ,
  (PrefixResourceState sorted_pages_2 x_pre y_pre (served + 1 ) (x - x ) (y - ((Znth served sorted_pages_2 0) - (2 * x ) ) ) )
.

Definition solver_entail_wit_2_2 := 
(
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages_2: (@list Z)) (PreH1 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) <= y)) (PreH2 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) > 0)) (PreH3 : (((Znth i sorted_pages_2 0) ÷ 2 ) <= x)) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : ((Zlength (sorted_pages_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (served = i)) (PreH11 : (0 <= x)) (PreH12 : (x <= x_pre)) (PreH13 : (0 <= y)) (PreH14 : (y <= y_pre)) (PreH15 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages_2 0)) /\ ((Znth j sorted_pages_2 0) <= 10000)))) (PreH16 : (Permutation page_counts sorted_pages_2 )) (PreH17 : (mono_nondec sorted_pages_2 )) (PreH18 : (PrefixResourceState sorted_pages_2 x_pre y_pre i x y )) ,
  (IntArray.full a_pre n_pre sorted_pages_2 )
|--
  EX (sorted_pages: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (sorted_pages)) = n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((served + 1 ) = (i + 1 )) ” 
  &&  “ (0 <= (x - ((Znth i sorted_pages_2 0) ÷ 2 ) )) ” 
  &&  “ ((x - ((Znth i sorted_pages_2 0) ÷ 2 ) ) <= x_pre) ” 
  &&  “ (0 <= (y - ((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) )) ” 
  &&  “ ((y - ((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) ) <= y_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000))) ” 
  &&  “ (Permutation page_counts sorted_pages ) ” 
  &&  “ (mono_nondec sorted_pages ) ” 
  &&  “ (PrefixResourceState sorted_pages x_pre y_pre (i + 1 ) (x - ((Znth i sorted_pages_2 0) ÷ 2 ) ) (y - ((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) ) ) ”
  &&  (IntArray.full a_pre n_pre sorted_pages )
) \/
(
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages_2: (@list Z)) (PreH1 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) <= y)) (PreH2 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) > 0)) (PreH3 : (((Znth i sorted_pages_2 0) ÷ 2 ) <= x)) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : ((Zlength (sorted_pages_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (served = i)) (PreH11 : (0 <= x)) (PreH12 : (x <= x_pre)) (PreH13 : (0 <= y)) (PreH14 : (y <= y_pre)) (PreH15 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages_2 0)) /\ ((Znth j sorted_pages_2 0) <= 10000)))) (PreH16 : (Permutation page_counts sorted_pages_2 )) (PreH17 : (mono_nondec sorted_pages_2 )) (PreH18 : (PrefixResourceState sorted_pages_2 x_pre y_pre i x y )) ,
  TT && emp 
|--
  “ (PrefixResourceState sorted_pages_2 x_pre y_pre (served + 1 ) (x - ((Znth served sorted_pages_2 0) ÷ 2 ) ) (y - ((Znth served sorted_pages_2 0) - (2 * ((Znth served sorted_pages_2 0) ÷ 2 ) ) ) ) ) ” 
  &&  “ ((x - ((Znth served sorted_pages_2 0) ÷ 2 ) ) <= x_pre) ”
  &&  emp
).

Definition solver_entail_wit_2_2_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages_2: (@list Z)) (PreH1 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) <= y)) (PreH2 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) > 0)) (PreH3 : (((Znth i sorted_pages_2 0) ÷ 2 ) <= x)) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : ((Zlength (sorted_pages_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (served = i)) (PreH11 : (0 <= x)) (PreH12 : (x <= x_pre)) (PreH13 : (0 <= y)) (PreH14 : (y <= y_pre)) (PreH15 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages_2 0)) /\ ((Znth j sorted_pages_2 0) <= 10000)))) (PreH16 : (Permutation page_counts sorted_pages_2 )) (PreH17 : (mono_nondec sorted_pages_2 )) (PreH18 : (PrefixResourceState sorted_pages_2 x_pre y_pre i x y )) ,
  (PrefixResourceState sorted_pages_2 x_pre y_pre (served + 1 ) (x - ((Znth served sorted_pages_2 0) ÷ 2 ) ) (y - ((Znth served sorted_pages_2 0) - (2 * ((Znth served sorted_pages_2 0) ÷ 2 ) ) ) ) )
.

Definition solver_entail_wit_2_2_split_goal_2 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages_2: (@list Z)) (PreH1 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) <= y)) (PreH2 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) > 0)) (PreH3 : (((Znth i sorted_pages_2 0) ÷ 2 ) <= x)) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : ((Zlength (sorted_pages_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (served = i)) (PreH11 : (0 <= x)) (PreH12 : (x <= x_pre)) (PreH13 : (0 <= y)) (PreH14 : (y <= y_pre)) (PreH15 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages_2 0)) /\ ((Znth j sorted_pages_2 0) <= 10000)))) (PreH16 : (Permutation page_counts sorted_pages_2 )) (PreH17 : (mono_nondec sorted_pages_2 )) (PreH18 : (PrefixResourceState sorted_pages_2 x_pre y_pre i x y )) ,
  ((x - ((Znth served sorted_pages_2 0) ÷ 2 ) ) <= x_pre)
.

Definition solver_entail_wit_2_3 := 
(
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages_2: (@list Z)) (PreH1 : ((x - ((Znth i sorted_pages_2 0) ÷ 2 ) ) > 0)) (PreH2 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) = 1)) (PreH3 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) > y)) (PreH4 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) > 0)) (PreH5 : (((Znth i sorted_pages_2 0) ÷ 2 ) <= x)) (PreH6 : (i < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((Zlength (sorted_pages_2)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (served = i)) (PreH13 : (0 <= x)) (PreH14 : (x <= x_pre)) (PreH15 : (0 <= y)) (PreH16 : (y <= y_pre)) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages_2 0)) /\ ((Znth j sorted_pages_2 0) <= 10000)))) (PreH18 : (Permutation page_counts sorted_pages_2 )) (PreH19 : (mono_nondec sorted_pages_2 )) (PreH20 : (PrefixResourceState sorted_pages_2 x_pre y_pre i x y )) ,
  (IntArray.full a_pre n_pre sorted_pages_2 )
|--
  EX (sorted_pages: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (sorted_pages)) = n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((served + 1 ) = (i + 1 )) ” 
  &&  “ (0 <= ((x - ((Znth i sorted_pages_2 0) ÷ 2 ) ) - 1 )) ” 
  &&  “ (((x - ((Znth i sorted_pages_2 0) ÷ 2 ) ) - 1 ) <= x_pre) ” 
  &&  “ (0 <= y) ” 
  &&  “ (y <= y_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000))) ” 
  &&  “ (Permutation page_counts sorted_pages ) ” 
  &&  “ (mono_nondec sorted_pages ) ” 
  &&  “ (PrefixResourceState sorted_pages x_pre y_pre (i + 1 ) ((x - ((Znth i sorted_pages_2 0) ÷ 2 ) ) - 1 ) y ) ”
  &&  (IntArray.full a_pre n_pre sorted_pages )
) \/
(
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages_2: (@list Z)) (PreH1 : ((x - ((Znth i sorted_pages_2 0) ÷ 2 ) ) > 0)) (PreH2 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) = 1)) (PreH3 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) > y)) (PreH4 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) > 0)) (PreH5 : (((Znth i sorted_pages_2 0) ÷ 2 ) <= x)) (PreH6 : (i < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((Zlength (sorted_pages_2)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (served = i)) (PreH13 : (0 <= x)) (PreH14 : (x <= x_pre)) (PreH15 : (0 <= y)) (PreH16 : (y <= y_pre)) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages_2 0)) /\ ((Znth j sorted_pages_2 0) <= 10000)))) (PreH18 : (Permutation page_counts sorted_pages_2 )) (PreH19 : (mono_nondec sorted_pages_2 )) (PreH20 : (PrefixResourceState sorted_pages_2 x_pre y_pre i x y )) ,
  TT && emp 
|--
  “ (PrefixResourceState sorted_pages_2 x_pre y_pre (served + 1 ) ((x - ((Znth served sorted_pages_2 0) ÷ 2 ) ) - 1 ) y ) ” 
  &&  “ (((x - ((Znth served sorted_pages_2 0) ÷ 2 ) ) - 1 ) <= x_pre) ”
  &&  emp
).

Definition solver_entail_wit_2_3_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages_2: (@list Z)) (PreH1 : ((x - ((Znth i sorted_pages_2 0) ÷ 2 ) ) > 0)) (PreH2 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) = 1)) (PreH3 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) > y)) (PreH4 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) > 0)) (PreH5 : (((Znth i sorted_pages_2 0) ÷ 2 ) <= x)) (PreH6 : (i < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((Zlength (sorted_pages_2)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (served = i)) (PreH13 : (0 <= x)) (PreH14 : (x <= x_pre)) (PreH15 : (0 <= y)) (PreH16 : (y <= y_pre)) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages_2 0)) /\ ((Znth j sorted_pages_2 0) <= 10000)))) (PreH18 : (Permutation page_counts sorted_pages_2 )) (PreH19 : (mono_nondec sorted_pages_2 )) (PreH20 : (PrefixResourceState sorted_pages_2 x_pre y_pre i x y )) ,
  (PrefixResourceState sorted_pages_2 x_pre y_pre (served + 1 ) ((x - ((Znth served sorted_pages_2 0) ÷ 2 ) ) - 1 ) y )
.

Definition solver_entail_wit_2_3_split_goal_2 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages_2: (@list Z)) (PreH1 : ((x - ((Znth i sorted_pages_2 0) ÷ 2 ) ) > 0)) (PreH2 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) = 1)) (PreH3 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) > y)) (PreH4 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) > 0)) (PreH5 : (((Znth i sorted_pages_2 0) ÷ 2 ) <= x)) (PreH6 : (i < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((Zlength (sorted_pages_2)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (served = i)) (PreH13 : (0 <= x)) (PreH14 : (x <= x_pre)) (PreH15 : (0 <= y)) (PreH16 : (y <= y_pre)) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages_2 0)) /\ ((Znth j sorted_pages_2 0) <= 10000)))) (PreH18 : (Permutation page_counts sorted_pages_2 )) (PreH19 : (mono_nondec sorted_pages_2 )) (PreH20 : (PrefixResourceState sorted_pages_2 x_pre y_pre i x y )) ,
  (((x - ((Znth served sorted_pages_2 0) ÷ 2 ) ) - 1 ) <= x_pre)
.

Definition solver_entail_wit_2_4 := 
(
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages_2: (@list Z)) (PreH1 : (((Znth i sorted_pages_2 0) - (2 * x ) ) <= 0)) (PreH2 : (((Znth i sorted_pages_2 0) ÷ 2 ) > x)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted_pages_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (served = i)) (PreH10 : (0 <= x)) (PreH11 : (x <= x_pre)) (PreH12 : (0 <= y)) (PreH13 : (y <= y_pre)) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages_2 0)) /\ ((Znth j sorted_pages_2 0) <= 10000)))) (PreH15 : (Permutation page_counts sorted_pages_2 )) (PreH16 : (mono_nondec sorted_pages_2 )) (PreH17 : (PrefixResourceState sorted_pages_2 x_pre y_pre i x y )) ,
  (IntArray.full a_pre n_pre sorted_pages_2 )
|--
  EX (sorted_pages: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (sorted_pages)) = n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((served + 1 ) = (i + 1 )) ” 
  &&  “ (0 <= (x - x )) ” 
  &&  “ ((x - x ) <= x_pre) ” 
  &&  “ (0 <= y) ” 
  &&  “ (y <= y_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000))) ” 
  &&  “ (Permutation page_counts sorted_pages ) ” 
  &&  “ (mono_nondec sorted_pages ) ” 
  &&  “ (PrefixResourceState sorted_pages x_pre y_pre (i + 1 ) (x - x ) y ) ”
  &&  (IntArray.full a_pre n_pre sorted_pages )
) \/
(
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages_2: (@list Z)) (PreH1 : (((Znth i sorted_pages_2 0) - (2 * x ) ) <= 0)) (PreH2 : (((Znth i sorted_pages_2 0) ÷ 2 ) > x)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted_pages_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (served = i)) (PreH10 : (0 <= x)) (PreH11 : (x <= x_pre)) (PreH12 : (0 <= y)) (PreH13 : (y <= y_pre)) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages_2 0)) /\ ((Znth j sorted_pages_2 0) <= 10000)))) (PreH15 : (Permutation page_counts sorted_pages_2 )) (PreH16 : (mono_nondec sorted_pages_2 )) (PreH17 : (PrefixResourceState sorted_pages_2 x_pre y_pre i x y )) ,
  TT && emp 
|--
  “ (PrefixResourceState sorted_pages_2 x_pre y_pre (served + 1 ) (x - x ) y ) ”
  &&  emp
).

Definition solver_entail_wit_2_4_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages_2: (@list Z)) (PreH1 : (((Znth i sorted_pages_2 0) - (2 * x ) ) <= 0)) (PreH2 : (((Znth i sorted_pages_2 0) ÷ 2 ) > x)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted_pages_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (served = i)) (PreH10 : (0 <= x)) (PreH11 : (x <= x_pre)) (PreH12 : (0 <= y)) (PreH13 : (y <= y_pre)) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages_2 0)) /\ ((Znth j sorted_pages_2 0) <= 10000)))) (PreH15 : (Permutation page_counts sorted_pages_2 )) (PreH16 : (mono_nondec sorted_pages_2 )) (PreH17 : (PrefixResourceState sorted_pages_2 x_pre y_pre i x y )) ,
  (PrefixResourceState sorted_pages_2 x_pre y_pre (served + 1 ) (x - x ) y )
.

Definition solver_entail_wit_2_5 := 
(
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages_2: (@list Z)) (PreH1 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) <= 0)) (PreH2 : (((Znth i sorted_pages_2 0) ÷ 2 ) <= x)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted_pages_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (served = i)) (PreH10 : (0 <= x)) (PreH11 : (x <= x_pre)) (PreH12 : (0 <= y)) (PreH13 : (y <= y_pre)) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages_2 0)) /\ ((Znth j sorted_pages_2 0) <= 10000)))) (PreH15 : (Permutation page_counts sorted_pages_2 )) (PreH16 : (mono_nondec sorted_pages_2 )) (PreH17 : (PrefixResourceState sorted_pages_2 x_pre y_pre i x y )) ,
  (IntArray.full a_pre n_pre sorted_pages_2 )
|--
  EX (sorted_pages: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (sorted_pages)) = n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((served + 1 ) = (i + 1 )) ” 
  &&  “ (0 <= (x - ((Znth i sorted_pages_2 0) ÷ 2 ) )) ” 
  &&  “ ((x - ((Znth i sorted_pages_2 0) ÷ 2 ) ) <= x_pre) ” 
  &&  “ (0 <= y) ” 
  &&  “ (y <= y_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000))) ” 
  &&  “ (Permutation page_counts sorted_pages ) ” 
  &&  “ (mono_nondec sorted_pages ) ” 
  &&  “ (PrefixResourceState sorted_pages x_pre y_pre (i + 1 ) (x - ((Znth i sorted_pages_2 0) ÷ 2 ) ) y ) ”
  &&  (IntArray.full a_pre n_pre sorted_pages )
) \/
(
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages_2: (@list Z)) (PreH1 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) <= 0)) (PreH2 : (((Znth i sorted_pages_2 0) ÷ 2 ) <= x)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted_pages_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (served = i)) (PreH10 : (0 <= x)) (PreH11 : (x <= x_pre)) (PreH12 : (0 <= y)) (PreH13 : (y <= y_pre)) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages_2 0)) /\ ((Znth j sorted_pages_2 0) <= 10000)))) (PreH15 : (Permutation page_counts sorted_pages_2 )) (PreH16 : (mono_nondec sorted_pages_2 )) (PreH17 : (PrefixResourceState sorted_pages_2 x_pre y_pre i x y )) ,
  TT && emp 
|--
  “ (PrefixResourceState sorted_pages_2 x_pre y_pre (served + 1 ) (x - ((Znth served sorted_pages_2 0) ÷ 2 ) ) y ) ”
  &&  emp
).

Definition solver_entail_wit_2_5_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages_2: (@list Z)) (PreH1 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) <= 0)) (PreH2 : (((Znth i sorted_pages_2 0) ÷ 2 ) <= x)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted_pages_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (served = i)) (PreH10 : (0 <= x)) (PreH11 : (x <= x_pre)) (PreH12 : (0 <= y)) (PreH13 : (y <= y_pre)) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages_2 0)) /\ ((Znth j sorted_pages_2 0) <= 10000)))) (PreH15 : (Permutation page_counts sorted_pages_2 )) (PreH16 : (mono_nondec sorted_pages_2 )) (PreH17 : (PrefixResourceState sorted_pages_2 x_pre y_pre i x y )) ,
  (PrefixResourceState sorted_pages_2 x_pre y_pre (served + 1 ) (x - ((Znth served sorted_pages_2 0) ÷ 2 ) ) y )
.

Definition solver_entail_wit_3_1 := 
(
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages_2: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (sorted_pages_2)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (served = i)) (PreH8 : (0 <= x)) (PreH9 : (x <= x_pre)) (PreH10 : (0 <= y)) (PreH11 : (y <= y_pre)) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages_2 0)) /\ ((Znth j sorted_pages_2 0) <= 10000)))) (PreH13 : (Permutation page_counts sorted_pages_2 )) (PreH14 : (mono_nondec sorted_pages_2 )) (PreH15 : (PrefixResourceState sorted_pages_2 x_pre y_pre i x y )) ,
  (IntArray.full a_pre n_pre sorted_pages_2 )
|--
  EX (sorted_pages: (@list Z)) ,
  “ (0 <= served) ” 
  &&  “ (served <= n_pre) ” 
  &&  “ (Spec page_counts x_pre y_pre served ) ” 
  &&  “ (Permutation page_counts sorted_pages ) ”
  &&  (IntArray.full a_pre n_pre sorted_pages )
) \/
(
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages_2: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (sorted_pages_2)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (served = i)) (PreH8 : (0 <= x)) (PreH9 : (x <= x_pre)) (PreH10 : (0 <= y)) (PreH11 : (y <= y_pre)) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages_2 0)) /\ ((Znth j sorted_pages_2 0) <= 10000)))) (PreH13 : (Permutation page_counts sorted_pages_2 )) (PreH14 : (mono_nondec sorted_pages_2 )) (PreH15 : (PrefixResourceState sorted_pages_2 x_pre y_pre i x y )) ,
  TT && emp 
|--
  “ (Spec page_counts x_pre y_pre served ) ”
  &&  emp
).

Definition solver_entail_wit_3_1_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages_2: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (sorted_pages_2)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (served = i)) (PreH8 : (0 <= x)) (PreH9 : (x <= x_pre)) (PreH10 : (0 <= y)) (PreH11 : (y <= y_pre)) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages_2 0)) /\ ((Znth j sorted_pages_2 0) <= 10000)))) (PreH13 : (Permutation page_counts sorted_pages_2 )) (PreH14 : (mono_nondec sorted_pages_2 )) (PreH15 : (PrefixResourceState sorted_pages_2 x_pre y_pre i x y )) ,
  (Spec page_counts x_pre y_pre served )
.

Definition solver_entail_wit_3_2 := 
(
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages_2: (@list Z)) (PreH1 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) <> 1)) (PreH2 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) > y)) (PreH3 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) > 0)) (PreH4 : (((Znth i sorted_pages_2 0) ÷ 2 ) <= x)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : ((Zlength (sorted_pages_2)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (served = i)) (PreH12 : (0 <= x)) (PreH13 : (x <= x_pre)) (PreH14 : (0 <= y)) (PreH15 : (y <= y_pre)) (PreH16 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages_2 0)) /\ ((Znth j sorted_pages_2 0) <= 10000)))) (PreH17 : (Permutation page_counts sorted_pages_2 )) (PreH18 : (mono_nondec sorted_pages_2 )) (PreH19 : (PrefixResourceState sorted_pages_2 x_pre y_pre i x y )) ,
  (IntArray.full a_pre n_pre sorted_pages_2 )
|--
  EX (sorted_pages: (@list Z)) ,
  “ (0 <= served) ” 
  &&  “ (served <= n_pre) ” 
  &&  “ (Spec page_counts x_pre y_pre served ) ” 
  &&  “ (Permutation page_counts sorted_pages ) ”
  &&  (IntArray.full a_pre n_pre sorted_pages )
) \/
(
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages_2: (@list Z)) (PreH1 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) <> 1)) (PreH2 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) > y)) (PreH3 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) > 0)) (PreH4 : (((Znth i sorted_pages_2 0) ÷ 2 ) <= x)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : ((Zlength (sorted_pages_2)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (served = i)) (PreH12 : (0 <= x)) (PreH13 : (x <= x_pre)) (PreH14 : (0 <= y)) (PreH15 : (y <= y_pre)) (PreH16 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages_2 0)) /\ ((Znth j sorted_pages_2 0) <= 10000)))) (PreH17 : (Permutation page_counts sorted_pages_2 )) (PreH18 : (mono_nondec sorted_pages_2 )) (PreH19 : (PrefixResourceState sorted_pages_2 x_pre y_pre i x y )) ,
  TT && emp 
|--
  “ (Spec page_counts x_pre y_pre served ) ”
  &&  emp
).

Definition solver_entail_wit_3_2_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages_2: (@list Z)) (PreH1 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) <> 1)) (PreH2 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) > y)) (PreH3 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) > 0)) (PreH4 : (((Znth i sorted_pages_2 0) ÷ 2 ) <= x)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : ((Zlength (sorted_pages_2)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (served = i)) (PreH12 : (0 <= x)) (PreH13 : (x <= x_pre)) (PreH14 : (0 <= y)) (PreH15 : (y <= y_pre)) (PreH16 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages_2 0)) /\ ((Znth j sorted_pages_2 0) <= 10000)))) (PreH17 : (Permutation page_counts sorted_pages_2 )) (PreH18 : (mono_nondec sorted_pages_2 )) (PreH19 : (PrefixResourceState sorted_pages_2 x_pre y_pre i x y )) ,
  (Spec page_counts x_pre y_pre served )
.

Definition solver_entail_wit_3_3 := 
(
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages_2: (@list Z)) (PreH1 : (((Znth i sorted_pages_2 0) - (2 * x ) ) <> 1)) (PreH2 : (((Znth i sorted_pages_2 0) - (2 * x ) ) > y)) (PreH3 : (((Znth i sorted_pages_2 0) - (2 * x ) ) > 0)) (PreH4 : (((Znth i sorted_pages_2 0) ÷ 2 ) > x)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : ((Zlength (sorted_pages_2)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (served = i)) (PreH12 : (0 <= x)) (PreH13 : (x <= x_pre)) (PreH14 : (0 <= y)) (PreH15 : (y <= y_pre)) (PreH16 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages_2 0)) /\ ((Znth j sorted_pages_2 0) <= 10000)))) (PreH17 : (Permutation page_counts sorted_pages_2 )) (PreH18 : (mono_nondec sorted_pages_2 )) (PreH19 : (PrefixResourceState sorted_pages_2 x_pre y_pre i x y )) ,
  (IntArray.full a_pre n_pre sorted_pages_2 )
|--
  EX (sorted_pages: (@list Z)) ,
  “ (0 <= served) ” 
  &&  “ (served <= n_pre) ” 
  &&  “ (Spec page_counts x_pre y_pre served ) ” 
  &&  “ (Permutation page_counts sorted_pages ) ”
  &&  (IntArray.full a_pre n_pre sorted_pages )
) \/
(
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages_2: (@list Z)) (PreH1 : (((Znth i sorted_pages_2 0) - (2 * x ) ) <> 1)) (PreH2 : (((Znth i sorted_pages_2 0) - (2 * x ) ) > y)) (PreH3 : (((Znth i sorted_pages_2 0) - (2 * x ) ) > 0)) (PreH4 : (((Znth i sorted_pages_2 0) ÷ 2 ) > x)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : ((Zlength (sorted_pages_2)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (served = i)) (PreH12 : (0 <= x)) (PreH13 : (x <= x_pre)) (PreH14 : (0 <= y)) (PreH15 : (y <= y_pre)) (PreH16 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages_2 0)) /\ ((Znth j sorted_pages_2 0) <= 10000)))) (PreH17 : (Permutation page_counts sorted_pages_2 )) (PreH18 : (mono_nondec sorted_pages_2 )) (PreH19 : (PrefixResourceState sorted_pages_2 x_pre y_pre i x y )) ,
  TT && emp 
|--
  “ (Spec page_counts x_pre y_pre served ) ”
  &&  emp
).

Definition solver_entail_wit_3_3_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages_2: (@list Z)) (PreH1 : (((Znth i sorted_pages_2 0) - (2 * x ) ) <> 1)) (PreH2 : (((Znth i sorted_pages_2 0) - (2 * x ) ) > y)) (PreH3 : (((Znth i sorted_pages_2 0) - (2 * x ) ) > 0)) (PreH4 : (((Znth i sorted_pages_2 0) ÷ 2 ) > x)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : ((Zlength (sorted_pages_2)) = n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (served = i)) (PreH12 : (0 <= x)) (PreH13 : (x <= x_pre)) (PreH14 : (0 <= y)) (PreH15 : (y <= y_pre)) (PreH16 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages_2 0)) /\ ((Znth j sorted_pages_2 0) <= 10000)))) (PreH17 : (Permutation page_counts sorted_pages_2 )) (PreH18 : (mono_nondec sorted_pages_2 )) (PreH19 : (PrefixResourceState sorted_pages_2 x_pre y_pre i x y )) ,
  (Spec page_counts x_pre y_pre served )
.

Definition solver_entail_wit_3_4 := 
(
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages_2: (@list Z)) (PreH1 : ((x - x ) <= 0)) (PreH2 : (((Znth i sorted_pages_2 0) - (2 * x ) ) = 1)) (PreH3 : (((Znth i sorted_pages_2 0) - (2 * x ) ) > y)) (PreH4 : (((Znth i sorted_pages_2 0) - (2 * x ) ) > 0)) (PreH5 : (((Znth i sorted_pages_2 0) ÷ 2 ) > x)) (PreH6 : (i < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((Zlength (sorted_pages_2)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (served = i)) (PreH13 : (0 <= x)) (PreH14 : (x <= x_pre)) (PreH15 : (0 <= y)) (PreH16 : (y <= y_pre)) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages_2 0)) /\ ((Znth j sorted_pages_2 0) <= 10000)))) (PreH18 : (Permutation page_counts sorted_pages_2 )) (PreH19 : (mono_nondec sorted_pages_2 )) (PreH20 : (PrefixResourceState sorted_pages_2 x_pre y_pre i x y )) ,
  (IntArray.full a_pre n_pre sorted_pages_2 )
|--
  EX (sorted_pages: (@list Z)) ,
  “ (0 <= served) ” 
  &&  “ (served <= n_pre) ” 
  &&  “ (Spec page_counts x_pre y_pre served ) ” 
  &&  “ (Permutation page_counts sorted_pages ) ”
  &&  (IntArray.full a_pre n_pre sorted_pages )
) \/
(
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages_2: (@list Z)) (PreH1 : ((x - x ) <= 0)) (PreH2 : (((Znth i sorted_pages_2 0) - (2 * x ) ) = 1)) (PreH3 : (((Znth i sorted_pages_2 0) - (2 * x ) ) > y)) (PreH4 : (((Znth i sorted_pages_2 0) - (2 * x ) ) > 0)) (PreH5 : (((Znth i sorted_pages_2 0) ÷ 2 ) > x)) (PreH6 : (i < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((Zlength (sorted_pages_2)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (served = i)) (PreH13 : (0 <= x)) (PreH14 : (x <= x_pre)) (PreH15 : (0 <= y)) (PreH16 : (y <= y_pre)) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages_2 0)) /\ ((Znth j sorted_pages_2 0) <= 10000)))) (PreH18 : (Permutation page_counts sorted_pages_2 )) (PreH19 : (mono_nondec sorted_pages_2 )) (PreH20 : (PrefixResourceState sorted_pages_2 x_pre y_pre i x y )) ,
  TT && emp 
|--
  “ (Spec page_counts x_pre y_pre served ) ”
  &&  emp
).

Definition solver_entail_wit_3_4_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages_2: (@list Z)) (PreH1 : ((x - x ) <= 0)) (PreH2 : (((Znth i sorted_pages_2 0) - (2 * x ) ) = 1)) (PreH3 : (((Znth i sorted_pages_2 0) - (2 * x ) ) > y)) (PreH4 : (((Znth i sorted_pages_2 0) - (2 * x ) ) > 0)) (PreH5 : (((Znth i sorted_pages_2 0) ÷ 2 ) > x)) (PreH6 : (i < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((Zlength (sorted_pages_2)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (served = i)) (PreH13 : (0 <= x)) (PreH14 : (x <= x_pre)) (PreH15 : (0 <= y)) (PreH16 : (y <= y_pre)) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages_2 0)) /\ ((Znth j sorted_pages_2 0) <= 10000)))) (PreH18 : (Permutation page_counts sorted_pages_2 )) (PreH19 : (mono_nondec sorted_pages_2 )) (PreH20 : (PrefixResourceState sorted_pages_2 x_pre y_pre i x y )) ,
  (Spec page_counts x_pre y_pre served )
.

Definition solver_entail_wit_3_5 := 
(
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages_2: (@list Z)) (PreH1 : ((x - ((Znth i sorted_pages_2 0) ÷ 2 ) ) <= 0)) (PreH2 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) = 1)) (PreH3 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) > y)) (PreH4 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) > 0)) (PreH5 : (((Znth i sorted_pages_2 0) ÷ 2 ) <= x)) (PreH6 : (i < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((Zlength (sorted_pages_2)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (served = i)) (PreH13 : (0 <= x)) (PreH14 : (x <= x_pre)) (PreH15 : (0 <= y)) (PreH16 : (y <= y_pre)) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages_2 0)) /\ ((Znth j sorted_pages_2 0) <= 10000)))) (PreH18 : (Permutation page_counts sorted_pages_2 )) (PreH19 : (mono_nondec sorted_pages_2 )) (PreH20 : (PrefixResourceState sorted_pages_2 x_pre y_pre i x y )) ,
  (IntArray.full a_pre n_pre sorted_pages_2 )
|--
  EX (sorted_pages: (@list Z)) ,
  “ (0 <= served) ” 
  &&  “ (served <= n_pre) ” 
  &&  “ (Spec page_counts x_pre y_pre served ) ” 
  &&  “ (Permutation page_counts sorted_pages ) ”
  &&  (IntArray.full a_pre n_pre sorted_pages )
) \/
(
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages_2: (@list Z)) (PreH1 : ((x - ((Znth i sorted_pages_2 0) ÷ 2 ) ) <= 0)) (PreH2 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) = 1)) (PreH3 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) > y)) (PreH4 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) > 0)) (PreH5 : (((Znth i sorted_pages_2 0) ÷ 2 ) <= x)) (PreH6 : (i < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((Zlength (sorted_pages_2)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (served = i)) (PreH13 : (0 <= x)) (PreH14 : (x <= x_pre)) (PreH15 : (0 <= y)) (PreH16 : (y <= y_pre)) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages_2 0)) /\ ((Znth j sorted_pages_2 0) <= 10000)))) (PreH18 : (Permutation page_counts sorted_pages_2 )) (PreH19 : (mono_nondec sorted_pages_2 )) (PreH20 : (PrefixResourceState sorted_pages_2 x_pre y_pre i x y )) ,
  TT && emp 
|--
  “ (Spec page_counts x_pre y_pre served ) ”
  &&  emp
).

Definition solver_entail_wit_3_5_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages_2: (@list Z)) (PreH1 : ((x - ((Znth i sorted_pages_2 0) ÷ 2 ) ) <= 0)) (PreH2 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) = 1)) (PreH3 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) > y)) (PreH4 : (((Znth i sorted_pages_2 0) - (2 * ((Znth i sorted_pages_2 0) ÷ 2 ) ) ) > 0)) (PreH5 : (((Znth i sorted_pages_2 0) ÷ 2 ) <= x)) (PreH6 : (i < n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((Zlength (sorted_pages_2)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (served = i)) (PreH13 : (0 <= x)) (PreH14 : (x <= x_pre)) (PreH15 : (0 <= y)) (PreH16 : (y <= y_pre)) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages_2 0)) /\ ((Znth j sorted_pages_2 0) <= 10000)))) (PreH18 : (Permutation page_counts sorted_pages_2 )) (PreH19 : (mono_nondec sorted_pages_2 )) (PreH20 : (PrefixResourceState sorted_pages_2 x_pre y_pre i x y )) ,
  (Spec page_counts x_pre y_pre served )
.

Definition solver_return_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (sorted_pages: (@list Z)) (served: Z) (PreH1 : (0 <= served)) (PreH2 : (served <= n_pre)) (PreH3 : (Spec page_counts x_pre y_pre served )) (PreH4 : (Permutation page_counts sorted_pages )) ,
  (IntArray.full a_pre n_pre sorted_pages )
|--
  EX (pages_after: (@list Z)) ,
  “ (Spec page_counts x_pre y_pre served ) ” 
  &&  “ (Permutation page_counts pages_after ) ”
  &&  (IntArray.full a_pre n_pre pages_after )
.

Definition solver_partial_solve_wit_1_pure := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (PreH1 : (x_pre >= 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i page_counts 0)) /\ ((Znth i page_counts 0) <= 10000)))) (PreH6 : (n_pre = (Zlength (page_counts)))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
  **  (IntArray.full a_pre n_pre page_counts )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ”
.

Definition solver_partial_solve_wit_1_aux := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (PreH1 : (x_pre >= 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i page_counts 0)) /\ ((Znth i page_counts 0) <= 10000)))) (PreH6 : (n_pre = (Zlength (page_counts)))) ,
  (IntArray.full a_pre n_pre page_counts )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (x_pre >= 0) ” 
  &&  “ (y_pre >= 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i page_counts 0)) /\ ((Znth i page_counts 0) <= 10000))) ” 
  &&  “ (n_pre = (Zlength (page_counts))) ”
  &&  (IntArray.full a_pre n_pre page_counts )
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (a_pre: Z) (page_counts: (@list Z)) (y: Z) (x: Z) (served: Z) (i: Z) (sorted_pages: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (sorted_pages)) = n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (served = i)) (PreH8 : (0 <= x)) (PreH9 : (x <= x_pre)) (PreH10 : (0 <= y)) (PreH11 : (y <= y_pre)) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000)))) (PreH13 : (Permutation page_counts sorted_pages )) (PreH14 : (mono_nondec sorted_pages )) (PreH15 : (PrefixResourceState sorted_pages x_pre y_pre i x y )) ,
  (IntArray.full a_pre n_pre sorted_pages )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (sorted_pages)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (served = i) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x <= x_pre) ” 
  &&  “ (0 <= y) ” 
  &&  “ (y <= y_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j sorted_pages 0)) /\ ((Znth j sorted_pages 0) <= 10000))) ” 
  &&  “ (Permutation page_counts sorted_pages ) ” 
  &&  “ (mono_nondec sorted_pages ) ” 
  &&  “ (PrefixResourceState sorted_pages x_pre y_pre i x y ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i sorted_pages 0))
  **  (IntArray.missing_i a_pre i 0 n_pre sorted_pages )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Axiom proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Axiom proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3.
Axiom proof_of_solver_entail_wit_2_4 : solver_entail_wit_2_4.
Axiom proof_of_solver_entail_wit_2_5 : solver_entail_wit_2_5.
Axiom proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1.
Axiom proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2.
Axiom proof_of_solver_entail_wit_3_3 : solver_entail_wit_3_3.
Axiom proof_of_solver_entail_wit_3_4 : solver_entail_wit_3_4.
Axiom proof_of_solver_entail_wit_3_5 : solver_entail_wit_3_5.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.

End VC_Correct.
