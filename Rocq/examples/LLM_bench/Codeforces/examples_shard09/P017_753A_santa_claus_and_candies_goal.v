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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P017_753A_santa_claus_and_candies_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (out_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) ,
  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (out_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) ,
  ((( &( "used" ) )) # Int64  |->_)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 := 
forall (out_pre: Z) (n_pre: Z) (used: Z) (k: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (0 <= k)) (PreH4 : (k <= n_pre)) (PreH5 : (used = (triangular (k)))) (PreH6 : (0 <= used)) (PreH7 : (used <= n_pre)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "used" ) )) # Int64  |-> used)
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ ((used + (k + 1 ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (used + (k + 1 ) )) ”
.

Definition solver_safety_wit_4 := 
forall (out_pre: Z) (n_pre: Z) (used: Z) (k: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (0 <= k)) (PreH4 : (k <= n_pre)) (PreH5 : (used = (triangular (k)))) (PreH6 : (0 <= used)) (PreH7 : (used <= n_pre)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "used" ) )) # Int64  |-> used)
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition solver_safety_wit_5 := 
forall (out_pre: Z) (n_pre: Z) (used: Z) (k: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (0 <= k)) (PreH4 : (k <= n_pre)) (PreH5 : (used = (triangular (k)))) (PreH6 : (0 <= used)) (PreH7 : (used <= n_pre)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "used" ) )) # Int64  |-> used)
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_6 := 
forall (out_pre: Z) (n_pre: Z) (used: Z) (k: Z) (PreH1 : ((used + (k + 1 ) ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : (0 <= used)) (PreH8 : (used <= n_pre)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "used" ) )) # Int64  |-> used)
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition solver_safety_wit_7 := 
forall (out_pre: Z) (n_pre: Z) (used: Z) (k: Z) (PreH1 : ((used + (k + 1 ) ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : (0 <= used)) (PreH8 : (used <= n_pre)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "used" ) )) # Int64  |-> used)
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ ((used + (k + 1 ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (used + (k + 1 ) )) ”
.

Definition solver_safety_wit_8 := 
forall (out_pre: Z) (n_pre: Z) (used: Z) (k: Z) (PreH1 : ((used + (k + 1 ) ) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : (0 <= used)) (PreH8 : (used <= n_pre)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "used" ) )) # Int64  |-> used)
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_9 := 
forall (out_pre: Z) (n_pre: Z) (written: (@list Z)) (i: Z) (used: Z) (k: Z) (PreH1 : (i < k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : (0 <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1 ) ))) (PreH10 : (0 <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written )) ,
  (IntArray.seg out_pre 0 (i + 1 ) (app (written) ((cons ((i + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg out_pre (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "used" ) )) # Int64  |-> used)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_10 := 
forall (out_pre: Z) (n_pre: Z) (written: (@list Z)) (i: Z) (used: Z) (k: Z) (PreH1 : (i < k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : (0 <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1 ) ))) (PreH10 : (0 <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "used" ) )) # Int64  |-> used)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg out_pre 0 i written )
  **  (IntArray.undef_seg out_pre i n_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_11 := 
forall (out_pre: Z) (n_pre: Z) (written: (@list Z)) (i: Z) (used: Z) (k: Z) (PreH1 : (i < k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : (0 <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1 ) ))) (PreH10 : (0 <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "used" ) )) # Int64  |-> used)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg out_pre 0 i written )
  **  (IntArray.undef_seg out_pre i n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_12 := 
forall (out_pre: Z) (n_pre: Z) (written: (@list Z)) (i: Z) (used: Z) (k: Z) (PreH1 : (i >= k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : (0 <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1 ) ))) (PreH10 : (0 <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "used" ) )) # Int64  |-> used)
  **  (IntArray.seg out_pre 0 i written )
  **  (IntArray.undef_seg out_pre i n_pre )
|--
  “ ((k - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - 1 )) ”
.

Definition solver_safety_wit_13 := 
forall (out_pre: Z) (n_pre: Z) (written: (@list Z)) (i: Z) (used: Z) (k: Z) (PreH1 : (i >= k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : (0 <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1 ) ))) (PreH10 : (0 <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "used" ) )) # Int64  |-> used)
  **  (IntArray.seg out_pre 0 i written )
  **  (IntArray.undef_seg out_pre i n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_14 := 
(
forall (out_pre: Z) (n_pre: Z) (written: (@list Z)) (i: Z) (used: Z) (k: Z) (PreH1 : (i >= k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : (0 <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1 ) ))) (PreH10 : (0 <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written )) ,
  (IntArray.seg out_pre 0 i written )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "used" ) )) # Int64  |-> used)
  **  (IntArray.undef_seg out_pre i n_pre )
|--
  “ (((Znth ((k - 1 ) - 0 ) written 0) + (n_pre - used ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth ((k - 1 ) - 0 ) written 0) + (n_pre - used ) )) ”
) \/
(
forall (out_pre: Z) (n_pre: Z) (written: (@list Z)) (i: Z) (used: Z) (k: Z) (PreH1 : (i >= k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : (0 <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1 ) ))) (PreH10 : (0 <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written )) ,
  (IntArray.seg out_pre 0 i written )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "used" ) )) # Int64  |-> used)
  **  (IntArray.undef_seg out_pre i n_pre )
|--
  “ (((Znth ((k - 1 ) - 0 ) written 0) + (n_pre - used ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth ((k - 1 ) - 0 ) written 0) + (n_pre - used ) )) ”
).

Definition solver_safety_wit_14_split_goal_1 := 
forall (out_pre: Z) (n_pre: Z) (written: (@list Z)) (i: Z) (used: Z) (k: Z) (PreH1 : (i >= k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : (0 <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1 ) ))) (PreH10 : (0 <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written )) ,
  (IntArray.seg out_pre 0 i written )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "used" ) )) # Int64  |-> used)
  **  (IntArray.undef_seg out_pre i n_pre )
|--
  “ (((Znth ((k - 1 ) - 0 ) written 0) + (n_pre - used ) ) <= INT_MAX) ”
.

Definition solver_safety_wit_14_split_goal_2 := 
forall (out_pre: Z) (n_pre: Z) (written: (@list Z)) (i: Z) (used: Z) (k: Z) (PreH1 : (i >= k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : (0 <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1 ) ))) (PreH10 : (0 <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written )) ,
  (IntArray.seg out_pre 0 i written )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "used" ) )) # Int64  |-> used)
  **  (IntArray.undef_seg out_pre i n_pre )
|--
  “ ((INT_MIN) <= ((Znth ((k - 1 ) - 0 ) written 0) + (n_pre - used ) )) ”
.

Definition solver_safety_wit_15 := 
forall (out_pre: Z) (n_pre: Z) (written: (@list Z)) (i: Z) (used: Z) (k: Z) (PreH1 : (i >= k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : (0 <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1 ) ))) (PreH10 : (0 <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written )) ,
  (IntArray.seg out_pre 0 i written )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "used" ) )) # Int64  |-> used)
  **  (IntArray.undef_seg out_pre i n_pre )
|--
  “ ((n_pre - used ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (n_pre - used )) ”
.

Definition solver_entail_wit_1 := 
(
forall (out_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) ,
  (IntArray.undef_full out_pre n_pre )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 = (triangular (0))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ”
  &&  (IntArray.undef_full out_pre n_pre )
) \/
(
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) ,
  TT && emp 
|--
  “ (0 = (triangular (0))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) ,
  (0 = (triangular (0)))
.

Definition solver_entail_wit_2 := 
(
forall (out_pre: Z) (n_pre: Z) (used: Z) (k: Z) (PreH1 : ((used + (k + 1 ) ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : (0 <= used)) (PreH8 : (used <= n_pre)) ,
  (IntArray.undef_full out_pre n_pre )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= n_pre) ” 
  &&  “ ((used + (k + 1 ) ) = (triangular ((k + 1 )))) ” 
  &&  “ (0 <= (used + (k + 1 ) )) ” 
  &&  “ ((used + (k + 1 ) ) <= n_pre) ”
  &&  (IntArray.undef_full out_pre n_pre )
) \/
(
forall (n_pre: Z) (used: Z) (k: Z) (PreH1 : ((used + (k + 1 ) ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : (0 <= used)) (PreH8 : (used <= n_pre)) ,
  TT && emp 
|--
  “ ((used + (k + 1 ) ) = (triangular ((k + 1 )))) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (used: Z) (k: Z) (PreH1 : ((used + (k + 1 ) ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : (0 <= used)) (PreH8 : (used <= n_pre)) ,
  ((used + (k + 1 ) ) = (triangular ((k + 1 ))))
.

Definition solver_entail_wit_3 := 
(
forall (out_pre: Z) (n_pre: Z) (used: Z) (k: Z) (PreH1 : ((used + (k + 1 ) ) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : (0 <= used)) (PreH8 : (used <= n_pre)) ,
  (IntArray.undef_full out_pre n_pre )
|--
  EX (written: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ (used = (triangular (k))) ” 
  &&  “ (0 <= used) ” 
  &&  “ (used <= n_pre) ” 
  &&  “ (n_pre < (used + (k + 1 ) )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= k) ” 
  &&  “ (CandyPrefix 0 written ) ”
  &&  (IntArray.seg out_pre 0 0 written )
  **  (IntArray.undef_seg out_pre 0 n_pre )
) \/
(
forall (n_pre: Z) (used: Z) (k: Z) (PreH1 : ((used + (k + 1 ) ) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : (0 <= used)) (PreH8 : (used <= n_pre)) ,
  TT && emp 
|--
  “ (CandyPrefix 0 (@nil Z) ) ” 
  &&  “ (1 <= k) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 := 
forall (n_pre: Z) (used: Z) (k: Z) (PreH1 : ((used + (k + 1 ) ) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : (0 <= used)) (PreH8 : (used <= n_pre)) ,
  (CandyPrefix 0 (@nil Z) )
.

Definition solver_entail_wit_3_split_goal_2 := 
forall (n_pre: Z) (used: Z) (k: Z) (PreH1 : ((used + (k + 1 ) ) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : (0 <= used)) (PreH8 : (used <= n_pre)) ,
  (1 <= k)
.

Definition solver_entail_wit_4 := 
(
forall (out_pre: Z) (n_pre: Z) (written_2: (@list Z)) (i: Z) (used: Z) (k: Z) (PreH1 : (i < k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : (0 <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1 ) ))) (PreH10 : (0 <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written_2 )) ,
  (IntArray.seg out_pre 0 (i + 1 ) (app (written_2) ((cons ((i + 1 )) ((@nil Z))))) )
  **  (IntArray.undef_seg out_pre (i + 1 ) n_pre )
|--
  EX (written: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ (used = (triangular (k))) ” 
  &&  “ (0 <= used) ” 
  &&  “ (used <= n_pre) ” 
  &&  “ (n_pre < (used + (k + 1 ) )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= k) ” 
  &&  “ (CandyPrefix (i + 1 ) written ) ”
  &&  (IntArray.seg out_pre 0 (i + 1 ) written )
  **  (IntArray.undef_seg out_pre (i + 1 ) n_pre )
) \/
(
forall (n_pre: Z) (written_2: (@list Z)) (i: Z) (used: Z) (k: Z) (PreH1 : (i < k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : (0 <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1 ) ))) (PreH10 : (0 <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written_2 )) ,
  TT && emp 
|--
  “ (CandyPrefix (i + 1 ) (app (written_2) ((cons ((i + 1 )) ((@nil Z))))) ) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 := 
forall (n_pre: Z) (written_2: (@list Z)) (i: Z) (used: Z) (k: Z) (PreH1 : (i < k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : (0 <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1 ) ))) (PreH10 : (0 <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written_2 )) ,
  (CandyPrefix (i + 1 ) (app (written_2) ((cons ((i + 1 )) ((@nil Z))))) )
.

Definition solver_entail_wit_5 := 
(
forall (out_pre: Z) (n_pre: Z) (written: (@list Z)) (i: Z) (used: Z) (k: Z) (PreH1 : (i >= k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : (0 <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1 ) ))) (PreH10 : (0 <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written )) ,
  (IntArray.full out_pre i (replace_Znth ((k - 1 )) (((Znth ((k - 1 ) - 0 ) written 0) + (n_pre - used ) )) (written)) )
  **  (IntArray.undef_seg out_pre i n_pre )
|--
  EX (out_spec: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ (used = (triangular (k))) ” 
  &&  “ (0 <= used) ” 
  &&  “ (used <= n_pre) ” 
  &&  “ (n_pre < (used + (k + 1 ) )) ” 
  &&  “ (GreedyCandyPlan n_pre k out_spec ) ” 
  &&  “ (Spec n_pre out_spec ) ”
  &&  (IntArray.full out_pre k out_spec )
  **  (IntArray.undef_seg out_pre k n_pre )
) \/
(
forall (out_pre: Z) (n_pre: Z) (written: (@list Z)) (i: Z) (used: Z) (k: Z) (PreH1 : (i >= k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : (0 <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1 ) ))) (PreH10 : (0 <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written )) ,
  (IntArray.full out_pre i (replace_Znth ((k - 1 )) (((Znth ((k - 1 ) - 0 ) written 0) + (n_pre - used ) )) (written)) )
|--
  EX (out_spec: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ (used = (triangular (k))) ” 
  &&  “ (0 <= used) ” 
  &&  “ (used <= n_pre) ” 
  &&  “ (n_pre < (used + (k + 1 ) )) ” 
  &&  “ (GreedyCandyPlan n_pre k out_spec ) ” 
  &&  “ (Spec n_pre out_spec ) ”
  &&  (IntArray.full out_pre k out_spec )
).

Definition solver_return_wit_1 := 
(
forall (out_pre: Z) (n_pre: Z) (out_spec_2: (@list Z)) (k: Z) (used: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (1 <= k)) (PreH4 : (k <= n_pre)) (PreH5 : (used = (triangular (k)))) (PreH6 : (0 <= used)) (PreH7 : (used <= n_pre)) (PreH8 : (n_pre < (used + (k + 1 ) ))) (PreH9 : (GreedyCandyPlan n_pre k out_spec_2 )) (PreH10 : (Spec n_pre out_spec_2 )) ,
  (IntArray.full out_pre k out_spec_2 )
  **  (IntArray.undef_seg out_pre k n_pre )
|--
  EX (out_spec: (@list Z)) ,
  “ (Spec n_pre out_spec ) ” 
  &&  “ (k = (Zlength (out_spec))) ”
  &&  (IntArray.full out_pre (Zlength (out_spec)) out_spec )
  **  (IntArray.undef_seg out_pre (Zlength (out_spec)) n_pre )
) \/
(
forall (out_pre: Z) (n_pre: Z) (out_spec_2: (@list Z)) (k: Z) (used: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (1 <= k)) (PreH4 : (k <= n_pre)) (PreH5 : (used = (triangular (k)))) (PreH6 : (0 <= used)) (PreH7 : (used <= n_pre)) (PreH8 : (n_pre < (used + (k + 1 ) ))) (PreH9 : (GreedyCandyPlan n_pre k out_spec_2 )) (PreH10 : (Spec n_pre out_spec_2 )) ,
  (IntArray.full out_pre k out_spec_2 )
  **  (IntArray.undef_seg out_pre k n_pre )
|--
  EX (out_spec: (@list Z)) ,
  “ (Spec n_pre out_spec ) ” 
  &&  “ (k = (Zlength (out_spec))) ”
  &&  (IntArray.full out_pre (Zlength (out_spec)) out_spec )
  **  (IntArray.undef_seg out_pre (Zlength (out_spec)) n_pre )
).

Definition solver_partial_solve_wit_1 := 
forall (out_pre: Z) (n_pre: Z) (written: (@list Z)) (i: Z) (used: Z) (k: Z) (PreH1 : (i < k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : (0 <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1 ) ))) (PreH10 : (0 <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written )) ,
  (IntArray.seg out_pre 0 i written )
  **  (IntArray.undef_seg out_pre i n_pre )
|--
  “ (i < k) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ (used = (triangular (k))) ” 
  &&  “ (0 <= used) ” 
  &&  “ (used <= n_pre) ” 
  &&  “ (n_pre < (used + (k + 1 ) )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= k) ” 
  &&  “ (CandyPrefix i written ) ”
  &&  (((out_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg out_pre (i + 1 ) n_pre )
  **  (IntArray.seg out_pre 0 i written )
.

Definition solver_partial_solve_wit_2 := 
forall (out_pre: Z) (n_pre: Z) (written: (@list Z)) (i: Z) (used: Z) (k: Z) (PreH1 : (i >= k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : (0 <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1 ) ))) (PreH10 : (0 <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written )) ,
  (IntArray.seg out_pre 0 i written )
  **  (IntArray.undef_seg out_pre i n_pre )
|--
  “ (i >= k) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ (used = (triangular (k))) ” 
  &&  “ (0 <= used) ” 
  &&  “ (used <= n_pre) ” 
  &&  “ (n_pre < (used + (k + 1 ) )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= k) ” 
  &&  “ (CandyPrefix i written ) ”
  &&  (((out_pre + ((k - 1 ) * sizeof(INT)))) # Int  |-> (Znth ((k - 1 ) - 0 ) written 0))
  **  (IntArray.missing_i out_pre (k - 1 ) 0 i written )
  **  (IntArray.undef_seg out_pre i n_pre )
.

Definition solver_partial_solve_wit_3 := 
forall (out_pre: Z) (n_pre: Z) (written: (@list Z)) (i: Z) (used: Z) (k: Z) (PreH1 : (i >= k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= k)) (PreH5 : (k <= n_pre)) (PreH6 : (used = (triangular (k)))) (PreH7 : (0 <= used)) (PreH8 : (used <= n_pre)) (PreH9 : (n_pre < (used + (k + 1 ) ))) (PreH10 : (0 <= i)) (PreH11 : (i <= k)) (PreH12 : (CandyPrefix i written )) ,
  (IntArray.seg out_pre 0 i written )
  **  (IntArray.undef_seg out_pre i n_pre )
|--
  “ (i >= k) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ (used = (triangular (k))) ” 
  &&  “ (0 <= used) ” 
  &&  “ (used <= n_pre) ” 
  &&  “ (n_pre < (used + (k + 1 ) )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= k) ” 
  &&  “ (CandyPrefix i written ) ”
  &&  (((out_pre + ((k - 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i out_pre (k - 1 ) 0 i written )
  **  (IntArray.undef_seg out_pre i n_pre )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.

End VC_Correct.
