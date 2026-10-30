From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P064_1992F_valuable_cards_lib.
Local Open Scope sac.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (PreH1 : (2 <= x_pre)) (PreH2 : (x_pre <= 100000)) (PreH3 : (1 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 100000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 200000)))) (PreH6 : (Pre x_pre values )) (PreH7 : (n_pre = (Zlength (values)))),
  ((( &( "used" ) )) # Ptr  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (PreH1 : (2 <= x_pre)) (PreH2 : (x_pre <= 100000)) (PreH3 : (1 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 100000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 200000)))) (PreH6 : (Pre x_pre values )) (PreH7 : (n_pre = (Zlength (values)))),
  ((( &( "used" ) )) # Ptr  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_3 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (2 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 200000)))) (PreH7 : (Pre x_pre values )) (PreH8 : (n_pre = (Zlength (values)))),
  ((( &( "products_buf" ) )) # Ptr  |->_)
  **  (UCharArray.full retval (x_pre + 1 ) (repeat_Z (0) ((x_pre + 1 ))) )
  **  ((( &( "used" ) )) # Ptr  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((x_pre + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (x_pre + 1 )) ”
.

Definition solver_safety_wit_4 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (2 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 200000)))) (PreH7 : (Pre x_pre values )) (PreH8 : (n_pre = (Zlength (values)))),
  ((( &( "products_buf" ) )) # Ptr  |->_)
  **  (UCharArray.full retval (x_pre + 1 ) (repeat_Z (0) ((x_pre + 1 ))) )
  **  ((( &( "used" ) )) # Ptr  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (n_pre = (Zlength (values)))),
  ((( &( "segments" ) )) # Int  |->_)
  **  ((( &( "count" ) )) # Int  |-> 1)
  **  (IntArray.undef_full retval_2 (x_pre + 1 ) )
  **  ((( &( "products_buf" ) )) # Ptr  |-> retval_2)
  **  (UCharArray.full retval (x_pre + 1 ) (repeat_Z (0) ((x_pre + 1 ))) )
  **  ((( &( "used" ) )) # Ptr  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_6 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (n_pre = (Zlength (values)))),
  ((( &( "count" ) )) # Int  |->_)
  **  (IntArray.undef_full retval_2 (x_pre + 1 ) )
  **  ((( &( "products_buf" ) )) # Ptr  |-> retval_2)
  **  (UCharArray.full retval (x_pre + 1 ) (repeat_Z (0) ((x_pre + 1 ))) )
  **  ((( &( "used" ) )) # Ptr  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_7 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (n_pre = (Zlength (values)))),
  ((( &( "segments" ) )) # Int  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> 1)
  **  (IntArray.undef_full retval_2 (x_pre + 1 ) )
  **  ((( &( "products_buf" ) )) # Ptr  |-> retval_2)
  **  (UCharArray.full retval (x_pre + 1 ) (repeat_Z (0) ((x_pre + 1 ))) )
  **  ((( &( "used" ) )) # Ptr  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_8 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (n_pre = (Zlength (values)))),
  ((( &( "segments" ) )) # Int  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> 1)
  **  (IntArray.undef_full retval_2 (x_pre + 1 ) )
  **  ((( &( "products_buf" ) )) # Ptr  |-> retval_2)
  **  (UCharArray.full retval (x_pre + 1 ) (repeat_Z (0) ((x_pre + 1 ))) )
  **  ((( &( "used" ) )) # Ptr  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_9 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (n_pre = (Zlength (values)))),
  (((retval_2 + (0 * sizeof(INT)))) # Int  |-> 1)
  **  (IntArray.undef_seg retval_2 1 (x_pre + 1 ) )
  **  ((( &( "segments" ) )) # Int  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> 1)
  **  ((( &( "products_buf" ) )) # Ptr  |-> retval_2)
  **  (UCharArray.full retval (x_pre + 1 ) (repeat_Z (0) ((x_pre + 1 ))) )
  **  ((( &( "used" ) )) # Ptr  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_10 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (n_pre = (Zlength (values)))),
  (((retval_2 + (0 * sizeof(INT)))) # Int  |-> 1)
  **  (IntArray.undef_seg retval_2 1 (x_pre + 1 ) )
  **  ((( &( "segments" ) )) # Int  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> 1)
  **  ((( &( "products_buf" ) )) # Ptr  |-> retval_2)
  **  (UCharArray.full retval (x_pre + 1 ) (repeat_Z (0) ((x_pre + 1 ))) )
  **  ((( &( "used" ) )) # Ptr  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_11 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (n_pre = (Zlength (values)))),
  ((( &( "i" ) )) # Int  |->_)
  **  (UCharArray.full retval (x_pre + 1 ) (replace_Znth (1) (1) ((repeat_Z (0) ((x_pre + 1 ))))) )
  **  (((retval_2 + (0 * sizeof(INT)))) # Int  |-> 1)
  **  (IntArray.undef_seg retval_2 1 (x_pre + 1 ) )
  **  ((( &( "segments" ) )) # Int  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> 1)
  **  ((( &( "products_buf" ) )) # Ptr  |-> retval_2)
  **  ((( &( "used" ) )) # Ptr  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_12 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (bitmap: (@list Z)) (products: (@list Z)) (count: Z) (segments: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= segments)) (PreH12 : (segments <= (i + 1 ))) (PreH13 : (count = (Zlength (products)))) (PreH14 : (1 <= count)) (PreH15 : (count <= x_pre)) (PreH16 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH17 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre)))) (PreH18 : (ValuableOuterState x_pre values i segments products )) (PreH19 : (ValuableForcedHistory x_pre values i segments products )) (PreH20 : (ValuableAlignedHistory x_pre values i segments products )) (PreH21 : (ValuableBitmap x_pre products bitmap )),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth i values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ ((x_pre <> (INT_MIN)) \/ ((Znth i values 0) <> (-1))) ”
  &&  “ ((Znth i values 0) <> 0) ”
.

Definition solver_safety_wit_13 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (bitmap: (@list Z)) (products: (@list Z)) (count: Z) (segments: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= segments)) (PreH12 : (segments <= (i + 1 ))) (PreH13 : (count = (Zlength (products)))) (PreH14 : (1 <= count)) (PreH15 : (count <= x_pre)) (PreH16 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH17 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre)))) (PreH18 : (ValuableOuterState x_pre values i segments products )) (PreH19 : (ValuableForcedHistory x_pre values i segments products )) (PreH20 : (ValuableAlignedHistory x_pre values i segments products )) (PreH21 : (ValuableBitmap x_pre products bitmap )) (PreH22 : ((x_pre % ( (Znth i values 0) ) ) = 0)),
  ((( &( "reaches" ) )) # Int  |->_)
  **  ((( &( "old" ) )) # Int  |-> count)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth i values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_14 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (bitmap: (@list Z)) (products: (@list Z)) (count: Z) (segments: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= segments)) (PreH12 : (segments <= (i + 1 ))) (PreH13 : (count = (Zlength (products)))) (PreH14 : (1 <= count)) (PreH15 : (count <= x_pre)) (PreH16 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH17 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre)))) (PreH18 : (ValuableOuterState x_pre values i segments products )) (PreH19 : (ValuableForcedHistory x_pre values i segments products )) (PreH20 : (ValuableAlignedHistory x_pre values i segments products )) (PreH21 : (ValuableBitmap x_pre products bitmap )) (PreH22 : ((x_pre % ( (Znth i values 0) ) ) = 0)),
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "reaches" ) )) # Int  |-> 0)
  **  ((( &( "old" ) )) # Int  |-> count)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "v" ) )) # Int  |-> (Znth i values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_15 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : (j < old)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (v = (Znth i values 0))) (PreH12 : (1 <= v)) (PreH13 : (v <= x_pre)) (PreH14 : ((x_pre % ( v ) ) = 0)) (PreH15 : (1 <= segments)) (PreH16 : (segments <= (i + 1 ))) (PreH17 : (old = (Zlength (base_products)))) (PreH18 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH19 : (1 <= old)) (PreH20 : (old <= count)) (PreH21 : (count <= x_pre)) (PreH22 : (0 <= j)) (PreH23 : (j <= old)) (PreH24 : (count = (Zlength (products_before_append)))) (PreH25 : (reaches = 0)) (PreH26 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH27 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH28 : (ValuableOuterState x_pre values i segments base_products )) (PreH29 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH30 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH31 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH32 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ ((x_pre <> (INT_MIN)) \/ (v <> (-1))) ”
  &&  “ (v <> 0) ”
.

Definition solver_safety_wit_16 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : (j < old)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (v = (Znth i values 0))) (PreH12 : (1 <= v)) (PreH13 : (v <= x_pre)) (PreH14 : ((x_pre % ( v ) ) = 0)) (PreH15 : (1 <= segments)) (PreH16 : (segments <= (i + 1 ))) (PreH17 : (old = (Zlength (base_products)))) (PreH18 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH19 : (1 <= old)) (PreH20 : (old <= count)) (PreH21 : (count <= x_pre)) (PreH22 : (0 <= j)) (PreH23 : (j <= old)) (PreH24 : (count = (Zlength (products_before_append)))) (PreH25 : (reaches = 1)) (PreH26 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH27 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH28 : (ValuableOuterState x_pre values i segments base_products )) (PreH29 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH30 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH31 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH32 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ ((x_pre <> (INT_MIN)) \/ (v <> (-1))) ”
  &&  “ (v <> 0) ”
.

Definition solver_safety_wit_17 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH2 : (j < old)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 100000)) (PreH6 : (1 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH9 : (Pre x_pre values )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (v = (Znth i values 0))) (PreH13 : (1 <= v)) (PreH14 : (v <= x_pre)) (PreH15 : ((x_pre % ( v ) ) = 0)) (PreH16 : (1 <= segments)) (PreH17 : (segments <= (i + 1 ))) (PreH18 : (old = (Zlength (base_products)))) (PreH19 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH20 : (1 <= old)) (PreH21 : (old <= count)) (PreH22 : (count <= x_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= old)) (PreH25 : (count = (Zlength (products_before_append)))) (PreH26 : (reaches = 1)) (PreH27 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH28 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH29 : (ValuableOuterState x_pre values i segments base_products )) (PreH30 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH31 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH32 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH33 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ ((x_pre <> (INT_MIN)) \/ (((Znth (j - 0 ) products_before_append 0) * v ) <> (-1))) ”
  &&  “ (((Znth (j - 0 ) products_before_append 0) * v ) <> 0) ”
.

Definition solver_safety_wit_18 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH2 : (j < old)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 100000)) (PreH6 : (1 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH9 : (Pre x_pre values )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (v = (Znth i values 0))) (PreH13 : (1 <= v)) (PreH14 : (v <= x_pre)) (PreH15 : ((x_pre % ( v ) ) = 0)) (PreH16 : (1 <= segments)) (PreH17 : (segments <= (i + 1 ))) (PreH18 : (old = (Zlength (base_products)))) (PreH19 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH20 : (1 <= old)) (PreH21 : (old <= count)) (PreH22 : (count <= x_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= old)) (PreH25 : (count = (Zlength (products_before_append)))) (PreH26 : (reaches = 0)) (PreH27 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH28 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH29 : (ValuableOuterState x_pre values i segments base_products )) (PreH30 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH31 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH32 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH33 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ ((x_pre <> (INT_MIN)) \/ (((Znth (j - 0 ) products_before_append 0) * v ) <> (-1))) ”
  &&  “ (((Znth (j - 0 ) products_before_append 0) * v ) <> 0) ”
.

Definition solver_safety_wit_19 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH2 : (j < old)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 100000)) (PreH6 : (1 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH9 : (Pre x_pre values )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (v = (Znth i values 0))) (PreH13 : (1 <= v)) (PreH14 : (v <= x_pre)) (PreH15 : ((x_pre % ( v ) ) = 0)) (PreH16 : (1 <= segments)) (PreH17 : (segments <= (i + 1 ))) (PreH18 : (old = (Zlength (base_products)))) (PreH19 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH20 : (1 <= old)) (PreH21 : (old <= count)) (PreH22 : (count <= x_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= old)) (PreH25 : (count = (Zlength (products_before_append)))) (PreH26 : (reaches = 1)) (PreH27 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH28 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH29 : (ValuableOuterState x_pre values i segments base_products )) (PreH30 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH31 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH32 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH33 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (((Znth (j - 0 ) products_before_append 0) * v ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth (j - 0 ) products_before_append 0) * v )) ”
) \/
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH2 : (j < old)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 100000)) (PreH6 : (1 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH9 : (Pre x_pre values )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (v = (Znth i values 0))) (PreH13 : (1 <= v)) (PreH14 : (v <= x_pre)) (PreH15 : ((x_pre % ( v ) ) = 0)) (PreH16 : (1 <= segments)) (PreH17 : (segments <= (i + 1 ))) (PreH18 : (old = (Zlength (base_products)))) (PreH19 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH20 : (1 <= old)) (PreH21 : (old <= count)) (PreH22 : (count <= x_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= old)) (PreH25 : (count = (Zlength (products_before_append)))) (PreH26 : (reaches = 1)) (PreH27 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH28 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH29 : (ValuableOuterState x_pre values i segments base_products )) (PreH30 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH31 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH32 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH33 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (((Znth (j - 0 ) products_before_append 0) * v ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth (j - 0 ) products_before_append 0) * v )) ”
).

Definition solver_safety_wit_19_split_goal_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH2 : (j < old)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 100000)) (PreH6 : (1 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH9 : (Pre x_pre values )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (v = (Znth i values 0))) (PreH13 : (1 <= v)) (PreH14 : (v <= x_pre)) (PreH15 : ((x_pre % ( v ) ) = 0)) (PreH16 : (1 <= segments)) (PreH17 : (segments <= (i + 1 ))) (PreH18 : (old = (Zlength (base_products)))) (PreH19 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH20 : (1 <= old)) (PreH21 : (old <= count)) (PreH22 : (count <= x_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= old)) (PreH25 : (count = (Zlength (products_before_append)))) (PreH26 : (reaches = 1)) (PreH27 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH28 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH29 : (ValuableOuterState x_pre values i segments base_products )) (PreH30 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH31 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH32 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH33 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (((Znth (j - 0 ) products_before_append 0) * v ) <= INT_MAX) ”
.

Definition solver_safety_wit_19_split_goal_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH2 : (j < old)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 100000)) (PreH6 : (1 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH9 : (Pre x_pre values )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (v = (Znth i values 0))) (PreH13 : (1 <= v)) (PreH14 : (v <= x_pre)) (PreH15 : ((x_pre % ( v ) ) = 0)) (PreH16 : (1 <= segments)) (PreH17 : (segments <= (i + 1 ))) (PreH18 : (old = (Zlength (base_products)))) (PreH19 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH20 : (1 <= old)) (PreH21 : (old <= count)) (PreH22 : (count <= x_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= old)) (PreH25 : (count = (Zlength (products_before_append)))) (PreH26 : (reaches = 1)) (PreH27 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH28 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH29 : (ValuableOuterState x_pre values i segments base_products )) (PreH30 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH31 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH32 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH33 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ ((INT_MIN) <= ((Znth (j - 0 ) products_before_append 0) * v )) ”
.

Definition solver_safety_wit_20 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH2 : (j < old)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 100000)) (PreH6 : (1 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH9 : (Pre x_pre values )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (v = (Znth i values 0))) (PreH13 : (1 <= v)) (PreH14 : (v <= x_pre)) (PreH15 : ((x_pre % ( v ) ) = 0)) (PreH16 : (1 <= segments)) (PreH17 : (segments <= (i + 1 ))) (PreH18 : (old = (Zlength (base_products)))) (PreH19 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH20 : (1 <= old)) (PreH21 : (old <= count)) (PreH22 : (count <= x_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= old)) (PreH25 : (count = (Zlength (products_before_append)))) (PreH26 : (reaches = 0)) (PreH27 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH28 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH29 : (ValuableOuterState x_pre values i segments base_products )) (PreH30 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH31 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH32 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH33 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (((Znth (j - 0 ) products_before_append 0) * v ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth (j - 0 ) products_before_append 0) * v )) ”
) \/
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH2 : (j < old)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 100000)) (PreH6 : (1 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH9 : (Pre x_pre values )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (v = (Znth i values 0))) (PreH13 : (1 <= v)) (PreH14 : (v <= x_pre)) (PreH15 : ((x_pre % ( v ) ) = 0)) (PreH16 : (1 <= segments)) (PreH17 : (segments <= (i + 1 ))) (PreH18 : (old = (Zlength (base_products)))) (PreH19 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH20 : (1 <= old)) (PreH21 : (old <= count)) (PreH22 : (count <= x_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= old)) (PreH25 : (count = (Zlength (products_before_append)))) (PreH26 : (reaches = 0)) (PreH27 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH28 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH29 : (ValuableOuterState x_pre values i segments base_products )) (PreH30 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH31 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH32 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH33 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (((Znth (j - 0 ) products_before_append 0) * v ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth (j - 0 ) products_before_append 0) * v )) ”
).

Definition solver_safety_wit_20_split_goal_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH2 : (j < old)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 100000)) (PreH6 : (1 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH9 : (Pre x_pre values )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (v = (Znth i values 0))) (PreH13 : (1 <= v)) (PreH14 : (v <= x_pre)) (PreH15 : ((x_pre % ( v ) ) = 0)) (PreH16 : (1 <= segments)) (PreH17 : (segments <= (i + 1 ))) (PreH18 : (old = (Zlength (base_products)))) (PreH19 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH20 : (1 <= old)) (PreH21 : (old <= count)) (PreH22 : (count <= x_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= old)) (PreH25 : (count = (Zlength (products_before_append)))) (PreH26 : (reaches = 0)) (PreH27 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH28 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH29 : (ValuableOuterState x_pre values i segments base_products )) (PreH30 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH31 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH32 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH33 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (((Znth (j - 0 ) products_before_append 0) * v ) <= INT_MAX) ”
.

Definition solver_safety_wit_20_split_goal_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH2 : (j < old)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 100000)) (PreH6 : (1 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH9 : (Pre x_pre values )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (v = (Znth i values 0))) (PreH13 : (1 <= v)) (PreH14 : (v <= x_pre)) (PreH15 : ((x_pre % ( v ) ) = 0)) (PreH16 : (1 <= segments)) (PreH17 : (segments <= (i + 1 ))) (PreH18 : (old = (Zlength (base_products)))) (PreH19 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH20 : (1 <= old)) (PreH21 : (old <= count)) (PreH22 : (count <= x_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= old)) (PreH25 : (count = (Zlength (products_before_append)))) (PreH26 : (reaches = 0)) (PreH27 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH28 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH29 : (ValuableOuterState x_pre values i segments base_products )) (PreH30 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH31 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH32 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH33 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ ((INT_MIN) <= ((Znth (j - 0 ) products_before_append 0) * v )) ”
.

Definition solver_safety_wit_21 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH2 : (j < old)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 100000)) (PreH6 : (1 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH9 : (Pre x_pre values )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (v = (Znth i values 0))) (PreH13 : (1 <= v)) (PreH14 : (v <= x_pre)) (PreH15 : ((x_pre % ( v ) ) = 0)) (PreH16 : (1 <= segments)) (PreH17 : (segments <= (i + 1 ))) (PreH18 : (old = (Zlength (base_products)))) (PreH19 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH20 : (1 <= old)) (PreH21 : (old <= count)) (PreH22 : (count <= x_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= old)) (PreH25 : (count = (Zlength (products_before_append)))) (PreH26 : (reaches = 0)) (PreH27 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH28 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH29 : (ValuableOuterState x_pre values i segments base_products )) (PreH30 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH31 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH32 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH33 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_22 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH2 : (j < old)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 100000)) (PreH6 : (1 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH9 : (Pre x_pre values )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (v = (Znth i values 0))) (PreH13 : (1 <= v)) (PreH14 : (v <= x_pre)) (PreH15 : ((x_pre % ( v ) ) = 0)) (PreH16 : (1 <= segments)) (PreH17 : (segments <= (i + 1 ))) (PreH18 : (old = (Zlength (base_products)))) (PreH19 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH20 : (1 <= old)) (PreH21 : (old <= count)) (PreH22 : (count <= x_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= old)) (PreH25 : (count = (Zlength (products_before_append)))) (PreH26 : (reaches = 1)) (PreH27 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH28 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH29 : (ValuableOuterState x_pre values i segments base_products )) (PreH30 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH31 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH32 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH33 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_23 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH2 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH3 : (j < old)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 100000)) (PreH7 : (1 <= (Zlength (values)))) (PreH8 : ((Zlength (values)) <= 100000)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH10 : (Pre x_pre values )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (v = (Znth i values 0))) (PreH14 : (1 <= v)) (PreH15 : (v <= x_pre)) (PreH16 : ((x_pre % ( v ) ) = 0)) (PreH17 : (1 <= segments)) (PreH18 : (segments <= (i + 1 ))) (PreH19 : (old = (Zlength (base_products)))) (PreH20 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH21 : (1 <= old)) (PreH22 : (old <= count)) (PreH23 : (count <= x_pre)) (PreH24 : (0 <= j)) (PreH25 : (j <= old)) (PreH26 : (count = (Zlength (products_before_append)))) (PreH27 : (reaches = 1)) (PreH28 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH29 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH30 : (ValuableOuterState x_pre values i segments base_products )) (PreH31 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH32 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH33 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH34 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (((Znth (j - 0 ) products_before_append 0) * v ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth (j - 0 ) products_before_append 0) * v )) ”
) \/
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH2 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH3 : (j < old)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 100000)) (PreH7 : (1 <= (Zlength (values)))) (PreH8 : ((Zlength (values)) <= 100000)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH10 : (Pre x_pre values )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (v = (Znth i values 0))) (PreH14 : (1 <= v)) (PreH15 : (v <= x_pre)) (PreH16 : ((x_pre % ( v ) ) = 0)) (PreH17 : (1 <= segments)) (PreH18 : (segments <= (i + 1 ))) (PreH19 : (old = (Zlength (base_products)))) (PreH20 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH21 : (1 <= old)) (PreH22 : (old <= count)) (PreH23 : (count <= x_pre)) (PreH24 : (0 <= j)) (PreH25 : (j <= old)) (PreH26 : (count = (Zlength (products_before_append)))) (PreH27 : (reaches = 1)) (PreH28 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH29 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH30 : (ValuableOuterState x_pre values i segments base_products )) (PreH31 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH32 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH33 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH34 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (((Znth (j - 0 ) products_before_append 0) * v ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth (j - 0 ) products_before_append 0) * v )) ”
).

Definition solver_safety_wit_23_split_goal_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH2 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH3 : (j < old)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 100000)) (PreH7 : (1 <= (Zlength (values)))) (PreH8 : ((Zlength (values)) <= 100000)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH10 : (Pre x_pre values )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (v = (Znth i values 0))) (PreH14 : (1 <= v)) (PreH15 : (v <= x_pre)) (PreH16 : ((x_pre % ( v ) ) = 0)) (PreH17 : (1 <= segments)) (PreH18 : (segments <= (i + 1 ))) (PreH19 : (old = (Zlength (base_products)))) (PreH20 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH21 : (1 <= old)) (PreH22 : (old <= count)) (PreH23 : (count <= x_pre)) (PreH24 : (0 <= j)) (PreH25 : (j <= old)) (PreH26 : (count = (Zlength (products_before_append)))) (PreH27 : (reaches = 1)) (PreH28 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH29 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH30 : (ValuableOuterState x_pre values i segments base_products )) (PreH31 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH32 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH33 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH34 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (((Znth (j - 0 ) products_before_append 0) * v ) <= INT_MAX) ”
.

Definition solver_safety_wit_23_split_goal_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH2 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH3 : (j < old)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 100000)) (PreH7 : (1 <= (Zlength (values)))) (PreH8 : ((Zlength (values)) <= 100000)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH10 : (Pre x_pre values )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (v = (Znth i values 0))) (PreH14 : (1 <= v)) (PreH15 : (v <= x_pre)) (PreH16 : ((x_pre % ( v ) ) = 0)) (PreH17 : (1 <= segments)) (PreH18 : (segments <= (i + 1 ))) (PreH19 : (old = (Zlength (base_products)))) (PreH20 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH21 : (1 <= old)) (PreH22 : (old <= count)) (PreH23 : (count <= x_pre)) (PreH24 : (0 <= j)) (PreH25 : (j <= old)) (PreH26 : (count = (Zlength (products_before_append)))) (PreH27 : (reaches = 1)) (PreH28 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH29 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH30 : (ValuableOuterState x_pre values i segments base_products )) (PreH31 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH32 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH33 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH34 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ ((INT_MIN) <= ((Znth (j - 0 ) products_before_append 0) * v )) ”
.

Definition solver_safety_wit_24 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH2 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH3 : (j < old)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 100000)) (PreH7 : (1 <= (Zlength (values)))) (PreH8 : ((Zlength (values)) <= 100000)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH10 : (Pre x_pre values )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (v = (Znth i values 0))) (PreH14 : (1 <= v)) (PreH15 : (v <= x_pre)) (PreH16 : ((x_pre % ( v ) ) = 0)) (PreH17 : (1 <= segments)) (PreH18 : (segments <= (i + 1 ))) (PreH19 : (old = (Zlength (base_products)))) (PreH20 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH21 : (1 <= old)) (PreH22 : (old <= count)) (PreH23 : (count <= x_pre)) (PreH24 : (0 <= j)) (PreH25 : (j <= old)) (PreH26 : (count = (Zlength (products_before_append)))) (PreH27 : (reaches = 0)) (PreH28 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH29 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH30 : (ValuableOuterState x_pre values i segments base_products )) (PreH31 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH32 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH33 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH34 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (((Znth (j - 0 ) products_before_append 0) * v ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth (j - 0 ) products_before_append 0) * v )) ”
) \/
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH2 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH3 : (j < old)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 100000)) (PreH7 : (1 <= (Zlength (values)))) (PreH8 : ((Zlength (values)) <= 100000)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH10 : (Pre x_pre values )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (v = (Znth i values 0))) (PreH14 : (1 <= v)) (PreH15 : (v <= x_pre)) (PreH16 : ((x_pre % ( v ) ) = 0)) (PreH17 : (1 <= segments)) (PreH18 : (segments <= (i + 1 ))) (PreH19 : (old = (Zlength (base_products)))) (PreH20 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH21 : (1 <= old)) (PreH22 : (old <= count)) (PreH23 : (count <= x_pre)) (PreH24 : (0 <= j)) (PreH25 : (j <= old)) (PreH26 : (count = (Zlength (products_before_append)))) (PreH27 : (reaches = 0)) (PreH28 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH29 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH30 : (ValuableOuterState x_pre values i segments base_products )) (PreH31 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH32 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH33 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH34 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (((Znth (j - 0 ) products_before_append 0) * v ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth (j - 0 ) products_before_append 0) * v )) ”
).

Definition solver_safety_wit_24_split_goal_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH2 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH3 : (j < old)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 100000)) (PreH7 : (1 <= (Zlength (values)))) (PreH8 : ((Zlength (values)) <= 100000)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH10 : (Pre x_pre values )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (v = (Znth i values 0))) (PreH14 : (1 <= v)) (PreH15 : (v <= x_pre)) (PreH16 : ((x_pre % ( v ) ) = 0)) (PreH17 : (1 <= segments)) (PreH18 : (segments <= (i + 1 ))) (PreH19 : (old = (Zlength (base_products)))) (PreH20 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH21 : (1 <= old)) (PreH22 : (old <= count)) (PreH23 : (count <= x_pre)) (PreH24 : (0 <= j)) (PreH25 : (j <= old)) (PreH26 : (count = (Zlength (products_before_append)))) (PreH27 : (reaches = 0)) (PreH28 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH29 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH30 : (ValuableOuterState x_pre values i segments base_products )) (PreH31 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH32 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH33 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH34 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (((Znth (j - 0 ) products_before_append 0) * v ) <= INT_MAX) ”
.

Definition solver_safety_wit_24_split_goal_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH2 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH3 : (j < old)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 100000)) (PreH7 : (1 <= (Zlength (values)))) (PreH8 : ((Zlength (values)) <= 100000)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH10 : (Pre x_pre values )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (v = (Znth i values 0))) (PreH14 : (1 <= v)) (PreH15 : (v <= x_pre)) (PreH16 : ((x_pre % ( v ) ) = 0)) (PreH17 : (1 <= segments)) (PreH18 : (segments <= (i + 1 ))) (PreH19 : (old = (Zlength (base_products)))) (PreH20 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH21 : (1 <= old)) (PreH22 : (old <= count)) (PreH23 : (count <= x_pre)) (PreH24 : (0 <= j)) (PreH25 : (j <= old)) (PreH26 : (count = (Zlength (products_before_append)))) (PreH27 : (reaches = 0)) (PreH28 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH29 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH30 : (ValuableOuterState x_pre values i segments base_products )) (PreH31 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH32 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH33 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH34 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ ((INT_MIN) <= ((Znth (j - 0 ) products_before_append 0) * v )) ”
.

Definition solver_safety_wit_25 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap 0) = 0)) (PreH2 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH3 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (j <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (old <= INT_MAX)) (PreH8 : (segments <= INT_MAX)) (PreH9 : (v <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (reaches >= INT_MIN)) (PreH13 : (j >= INT_MIN)) (PreH14 : (count >= INT_MIN)) (PreH15 : (old >= INT_MIN)) (PreH16 : (segments >= INT_MIN)) (PreH17 : (v >= INT_MIN)) (PreH18 : (i >= INT_MIN)) (PreH19 : (n_pre >= INT_MIN)) (PreH20 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH21 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH22 : (j < old)) (PreH23 : (n_pre = (Zlength (values)))) (PreH24 : (2 <= x_pre)) (PreH25 : (x_pre <= 100000)) (PreH26 : (1 <= (Zlength (values)))) (PreH27 : ((Zlength (values)) <= 100000)) (PreH28 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH29 : (Pre x_pre values )) (PreH30 : (0 <= i)) (PreH31 : (i < n_pre)) (PreH32 : (v = (Znth i values 0))) (PreH33 : (1 <= v)) (PreH34 : (v <= x_pre)) (PreH35 : ((x_pre % ( v ) ) = 0)) (PreH36 : (1 <= segments)) (PreH37 : (segments <= (i + 1 ))) (PreH38 : (old = (Zlength (base_products)))) (PreH39 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH40 : (1 <= old)) (PreH41 : (old <= count)) (PreH42 : (count <= x_pre)) (PreH43 : (0 <= j)) (PreH44 : (j <= old)) (PreH45 : (count = (Zlength (products_before_append)))) (PreH46 : (reaches = 1)) (PreH47 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH48 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH49 : (ValuableOuterState x_pre values i segments base_products )) (PreH50 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH51 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH52 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH53 : (ValuableBitmap x_pre products_before_append bitmap )),
  (UCharArray.full used (x_pre + 1 ) bitmap )
  **  ((( &( "p" ) )) # Int  |-> ((Znth (j - 0 ) products_before_append 0) * v ))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_26 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap 0) = 0)) (PreH2 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH3 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (j <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (old <= INT_MAX)) (PreH8 : (segments <= INT_MAX)) (PreH9 : (v <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (reaches >= INT_MIN)) (PreH13 : (j >= INT_MIN)) (PreH14 : (count >= INT_MIN)) (PreH15 : (old >= INT_MIN)) (PreH16 : (segments >= INT_MIN)) (PreH17 : (v >= INT_MIN)) (PreH18 : (i >= INT_MIN)) (PreH19 : (n_pre >= INT_MIN)) (PreH20 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH21 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH22 : (j < old)) (PreH23 : (n_pre = (Zlength (values)))) (PreH24 : (2 <= x_pre)) (PreH25 : (x_pre <= 100000)) (PreH26 : (1 <= (Zlength (values)))) (PreH27 : ((Zlength (values)) <= 100000)) (PreH28 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH29 : (Pre x_pre values )) (PreH30 : (0 <= i)) (PreH31 : (i < n_pre)) (PreH32 : (v = (Znth i values 0))) (PreH33 : (1 <= v)) (PreH34 : (v <= x_pre)) (PreH35 : ((x_pre % ( v ) ) = 0)) (PreH36 : (1 <= segments)) (PreH37 : (segments <= (i + 1 ))) (PreH38 : (old = (Zlength (base_products)))) (PreH39 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH40 : (1 <= old)) (PreH41 : (old <= count)) (PreH42 : (count <= x_pre)) (PreH43 : (0 <= j)) (PreH44 : (j <= old)) (PreH45 : (count = (Zlength (products_before_append)))) (PreH46 : (reaches = 0)) (PreH47 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH48 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH49 : (ValuableOuterState x_pre values i segments base_products )) (PreH50 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH51 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH52 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH53 : (ValuableBitmap x_pre products_before_append bitmap )),
  (UCharArray.full used (x_pre + 1 ) bitmap )
  **  ((( &( "p" ) )) # Int  |-> ((Znth (j - 0 ) products_before_append 0) * v ))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_27 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap 0) = 0)) (PreH2 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH3 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (j <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (old <= INT_MAX)) (PreH8 : (segments <= INT_MAX)) (PreH9 : (v <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (reaches >= INT_MIN)) (PreH13 : (j >= INT_MIN)) (PreH14 : (count >= INT_MIN)) (PreH15 : (old >= INT_MIN)) (PreH16 : (segments >= INT_MIN)) (PreH17 : (v >= INT_MIN)) (PreH18 : (i >= INT_MIN)) (PreH19 : (n_pre >= INT_MIN)) (PreH20 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH21 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH22 : (j < old)) (PreH23 : (n_pre = (Zlength (values)))) (PreH24 : (2 <= x_pre)) (PreH25 : (x_pre <= 100000)) (PreH26 : (1 <= (Zlength (values)))) (PreH27 : ((Zlength (values)) <= 100000)) (PreH28 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH29 : (Pre x_pre values )) (PreH30 : (0 <= i)) (PreH31 : (i < n_pre)) (PreH32 : (v = (Znth i values 0))) (PreH33 : (1 <= v)) (PreH34 : (v <= x_pre)) (PreH35 : ((x_pre % ( v ) ) = 0)) (PreH36 : (1 <= segments)) (PreH37 : (segments <= (i + 1 ))) (PreH38 : (old = (Zlength (base_products)))) (PreH39 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH40 : (1 <= old)) (PreH41 : (old <= count)) (PreH42 : (count <= x_pre)) (PreH43 : (0 <= j)) (PreH44 : (j <= old)) (PreH45 : (count = (Zlength (products_before_append)))) (PreH46 : (reaches = 1)) (PreH47 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH48 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH49 : (ValuableOuterState x_pre values i segments base_products )) (PreH50 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH51 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH52 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH53 : (ValuableBitmap x_pre products_before_append bitmap )),
  ((( &( "p" ) )) # Int  |-> ((Znth (j - 0 ) products_before_append 0) * v ))
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.seg products_buf 0 (count + 1 ) (app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * v )) ((@nil Z))))) )
  **  (IntArray.undef_seg products_buf (count + 1 ) (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) (replace_Znth (((Znth (j - 0 ) products_before_append 0) * v )) (1) (bitmap)) )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "used" ) )) # Ptr  |-> used)
|--
  “ ((count + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition solver_safety_wit_28 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap 0) = 0)) (PreH2 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH3 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (j <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (old <= INT_MAX)) (PreH8 : (segments <= INT_MAX)) (PreH9 : (v <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (reaches >= INT_MIN)) (PreH13 : (j >= INT_MIN)) (PreH14 : (count >= INT_MIN)) (PreH15 : (old >= INT_MIN)) (PreH16 : (segments >= INT_MIN)) (PreH17 : (v >= INT_MIN)) (PreH18 : (i >= INT_MIN)) (PreH19 : (n_pre >= INT_MIN)) (PreH20 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH21 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH22 : (j < old)) (PreH23 : (n_pre = (Zlength (values)))) (PreH24 : (2 <= x_pre)) (PreH25 : (x_pre <= 100000)) (PreH26 : (1 <= (Zlength (values)))) (PreH27 : ((Zlength (values)) <= 100000)) (PreH28 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH29 : (Pre x_pre values )) (PreH30 : (0 <= i)) (PreH31 : (i < n_pre)) (PreH32 : (v = (Znth i values 0))) (PreH33 : (1 <= v)) (PreH34 : (v <= x_pre)) (PreH35 : ((x_pre % ( v ) ) = 0)) (PreH36 : (1 <= segments)) (PreH37 : (segments <= (i + 1 ))) (PreH38 : (old = (Zlength (base_products)))) (PreH39 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH40 : (1 <= old)) (PreH41 : (old <= count)) (PreH42 : (count <= x_pre)) (PreH43 : (0 <= j)) (PreH44 : (j <= old)) (PreH45 : (count = (Zlength (products_before_append)))) (PreH46 : (reaches = 0)) (PreH47 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH48 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH49 : (ValuableOuterState x_pre values i segments base_products )) (PreH50 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH51 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH52 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH53 : (ValuableBitmap x_pre products_before_append bitmap )),
  ((( &( "p" ) )) # Int  |-> ((Znth (j - 0 ) products_before_append 0) * v ))
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.seg products_buf 0 (count + 1 ) (app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * v )) ((@nil Z))))) )
  **  (IntArray.undef_seg products_buf (count + 1 ) (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) (replace_Znth (((Znth (j - 0 ) products_before_append 0) * v )) (1) (bitmap)) )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "used" ) )) # Ptr  |-> used)
|--
  “ ((count + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition solver_safety_wit_29 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : (((Znth (j - 0 ) products_before_append 0) * v ) = x_pre)) (PreH2 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap 0) = 0)) (PreH3 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH4 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH5 : (reaches <= INT_MAX)) (PreH6 : (j <= INT_MAX)) (PreH7 : (count <= INT_MAX)) (PreH8 : (old <= INT_MAX)) (PreH9 : (segments <= INT_MAX)) (PreH10 : (v <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (reaches >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (count >= INT_MIN)) (PreH16 : (old >= INT_MIN)) (PreH17 : (segments >= INT_MIN)) (PreH18 : (v >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH22 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH23 : (j < old)) (PreH24 : (n_pre = (Zlength (values)))) (PreH25 : (2 <= x_pre)) (PreH26 : (x_pre <= 100000)) (PreH27 : (1 <= (Zlength (values)))) (PreH28 : ((Zlength (values)) <= 100000)) (PreH29 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH30 : (Pre x_pre values )) (PreH31 : (0 <= i)) (PreH32 : (i < n_pre)) (PreH33 : (v = (Znth i values 0))) (PreH34 : (1 <= v)) (PreH35 : (v <= x_pre)) (PreH36 : ((x_pre % ( v ) ) = 0)) (PreH37 : (1 <= segments)) (PreH38 : (segments <= (i + 1 ))) (PreH39 : (old = (Zlength (base_products)))) (PreH40 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH41 : (1 <= old)) (PreH42 : (old <= count)) (PreH43 : (count <= x_pre)) (PreH44 : (0 <= j)) (PreH45 : (j <= old)) (PreH46 : (count = (Zlength (products_before_append)))) (PreH47 : (reaches = 1)) (PreH48 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH49 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH50 : (ValuableOuterState x_pre values i segments base_products )) (PreH51 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH52 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH53 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH54 : (ValuableBitmap x_pre products_before_append bitmap )),
  ((( &( "p" ) )) # Int  |-> ((Znth (j - 0 ) products_before_append 0) * v ))
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.seg products_buf 0 (count + 1 ) (app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * v )) ((@nil Z))))) )
  **  (IntArray.undef_seg products_buf (count + 1 ) (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) (replace_Znth (((Znth (j - 0 ) products_before_append 0) * v )) (1) (bitmap)) )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "used" ) )) # Ptr  |-> used)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_30 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : (((Znth (j - 0 ) products_before_append 0) * v ) = x_pre)) (PreH2 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap 0) = 0)) (PreH3 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH4 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH5 : (reaches <= INT_MAX)) (PreH6 : (j <= INT_MAX)) (PreH7 : (count <= INT_MAX)) (PreH8 : (old <= INT_MAX)) (PreH9 : (segments <= INT_MAX)) (PreH10 : (v <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (reaches >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (count >= INT_MIN)) (PreH16 : (old >= INT_MIN)) (PreH17 : (segments >= INT_MIN)) (PreH18 : (v >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH22 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH23 : (j < old)) (PreH24 : (n_pre = (Zlength (values)))) (PreH25 : (2 <= x_pre)) (PreH26 : (x_pre <= 100000)) (PreH27 : (1 <= (Zlength (values)))) (PreH28 : ((Zlength (values)) <= 100000)) (PreH29 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH30 : (Pre x_pre values )) (PreH31 : (0 <= i)) (PreH32 : (i < n_pre)) (PreH33 : (v = (Znth i values 0))) (PreH34 : (1 <= v)) (PreH35 : (v <= x_pre)) (PreH36 : ((x_pre % ( v ) ) = 0)) (PreH37 : (1 <= segments)) (PreH38 : (segments <= (i + 1 ))) (PreH39 : (old = (Zlength (base_products)))) (PreH40 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH41 : (1 <= old)) (PreH42 : (old <= count)) (PreH43 : (count <= x_pre)) (PreH44 : (0 <= j)) (PreH45 : (j <= old)) (PreH46 : (count = (Zlength (products_before_append)))) (PreH47 : (reaches = 0)) (PreH48 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH49 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH50 : (ValuableOuterState x_pre values i segments base_products )) (PreH51 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH52 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH53 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH54 : (ValuableBitmap x_pre products_before_append bitmap )),
  ((( &( "p" ) )) # Int  |-> ((Znth (j - 0 ) products_before_append 0) * v ))
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.seg products_buf 0 (count + 1 ) (app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * v )) ((@nil Z))))) )
  **  (IntArray.undef_seg products_buf (count + 1 ) (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) (replace_Znth (((Znth (j - 0 ) products_before_append 0) * v )) (1) (bitmap)) )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "used" ) )) # Ptr  |-> used)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_31 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : (((Znth (j - 0 ) products_before_append 0) * v ) = x_pre)) (PreH2 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap 0) <> 0)) (PreH3 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH4 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH5 : (reaches <= INT_MAX)) (PreH6 : (j <= INT_MAX)) (PreH7 : (count <= INT_MAX)) (PreH8 : (old <= INT_MAX)) (PreH9 : (segments <= INT_MAX)) (PreH10 : (v <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (reaches >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (count >= INT_MIN)) (PreH16 : (old >= INT_MIN)) (PreH17 : (segments >= INT_MIN)) (PreH18 : (v >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH22 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH23 : (j < old)) (PreH24 : (n_pre = (Zlength (values)))) (PreH25 : (2 <= x_pre)) (PreH26 : (x_pre <= 100000)) (PreH27 : (1 <= (Zlength (values)))) (PreH28 : ((Zlength (values)) <= 100000)) (PreH29 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH30 : (Pre x_pre values )) (PreH31 : (0 <= i)) (PreH32 : (i < n_pre)) (PreH33 : (v = (Znth i values 0))) (PreH34 : (1 <= v)) (PreH35 : (v <= x_pre)) (PreH36 : ((x_pre % ( v ) ) = 0)) (PreH37 : (1 <= segments)) (PreH38 : (segments <= (i + 1 ))) (PreH39 : (old = (Zlength (base_products)))) (PreH40 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH41 : (1 <= old)) (PreH42 : (old <= count)) (PreH43 : (count <= x_pre)) (PreH44 : (0 <= j)) (PreH45 : (j <= old)) (PreH46 : (count = (Zlength (products_before_append)))) (PreH47 : (reaches = 1)) (PreH48 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH49 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH50 : (ValuableOuterState x_pre values i segments base_products )) (PreH51 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH52 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH53 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH54 : (ValuableBitmap x_pre products_before_append bitmap )),
  (UCharArray.full used (x_pre + 1 ) bitmap )
  **  ((( &( "p" ) )) # Int  |-> ((Znth (j - 0 ) products_before_append 0) * v ))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_32 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : (((Znth (j - 0 ) products_before_append 0) * v ) = x_pre)) (PreH2 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap 0) <> 0)) (PreH3 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH4 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH5 : (reaches <= INT_MAX)) (PreH6 : (j <= INT_MAX)) (PreH7 : (count <= INT_MAX)) (PreH8 : (old <= INT_MAX)) (PreH9 : (segments <= INT_MAX)) (PreH10 : (v <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (reaches >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (count >= INT_MIN)) (PreH16 : (old >= INT_MIN)) (PreH17 : (segments >= INT_MIN)) (PreH18 : (v >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH22 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH23 : (j < old)) (PreH24 : (n_pre = (Zlength (values)))) (PreH25 : (2 <= x_pre)) (PreH26 : (x_pre <= 100000)) (PreH27 : (1 <= (Zlength (values)))) (PreH28 : ((Zlength (values)) <= 100000)) (PreH29 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH30 : (Pre x_pre values )) (PreH31 : (0 <= i)) (PreH32 : (i < n_pre)) (PreH33 : (v = (Znth i values 0))) (PreH34 : (1 <= v)) (PreH35 : (v <= x_pre)) (PreH36 : ((x_pre % ( v ) ) = 0)) (PreH37 : (1 <= segments)) (PreH38 : (segments <= (i + 1 ))) (PreH39 : (old = (Zlength (base_products)))) (PreH40 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH41 : (1 <= old)) (PreH42 : (old <= count)) (PreH43 : (count <= x_pre)) (PreH44 : (0 <= j)) (PreH45 : (j <= old)) (PreH46 : (count = (Zlength (products_before_append)))) (PreH47 : (reaches = 0)) (PreH48 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH49 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH50 : (ValuableOuterState x_pre values i segments base_products )) (PreH51 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH52 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH53 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH54 : (ValuableBitmap x_pre products_before_append bitmap )),
  (UCharArray.full used (x_pre + 1 ) bitmap )
  **  ((( &( "p" ) )) # Int  |-> ((Znth (j - 0 ) products_before_append 0) * v ))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_33 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : (((Znth (j - 0 ) products_before_append 0) * v ) = x_pre)) (PreH2 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap 0) = 0)) (PreH3 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH4 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH5 : (reaches <= INT_MAX)) (PreH6 : (j <= INT_MAX)) (PreH7 : (count <= INT_MAX)) (PreH8 : (old <= INT_MAX)) (PreH9 : (segments <= INT_MAX)) (PreH10 : (v <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (reaches >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (count >= INT_MIN)) (PreH16 : (old >= INT_MIN)) (PreH17 : (segments >= INT_MIN)) (PreH18 : (v >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH22 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH23 : (j < old)) (PreH24 : (n_pre = (Zlength (values)))) (PreH25 : (2 <= x_pre)) (PreH26 : (x_pre <= 100000)) (PreH27 : (1 <= (Zlength (values)))) (PreH28 : ((Zlength (values)) <= 100000)) (PreH29 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH30 : (Pre x_pre values )) (PreH31 : (0 <= i)) (PreH32 : (i < n_pre)) (PreH33 : (v = (Znth i values 0))) (PreH34 : (1 <= v)) (PreH35 : (v <= x_pre)) (PreH36 : ((x_pre % ( v ) ) = 0)) (PreH37 : (1 <= segments)) (PreH38 : (segments <= (i + 1 ))) (PreH39 : (old = (Zlength (base_products)))) (PreH40 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH41 : (1 <= old)) (PreH42 : (old <= count)) (PreH43 : (count <= x_pre)) (PreH44 : (0 <= j)) (PreH45 : (j <= old)) (PreH46 : (count = (Zlength (products_before_append)))) (PreH47 : (reaches = 1)) (PreH48 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH49 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH50 : (ValuableOuterState x_pre values i segments base_products )) (PreH51 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH52 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH53 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH54 : (ValuableBitmap x_pre products_before_append bitmap )),
  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.seg products_buf 0 (count + 1 ) (app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * v )) ((@nil Z))))) )
  **  (IntArray.undef_seg products_buf (count + 1 ) (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) (replace_Znth (((Znth (j - 0 ) products_before_append 0) * v )) (1) (bitmap)) )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> 1)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "used" ) )) # Ptr  |-> used)
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_34 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : (((Znth (j - 0 ) products_before_append 0) * v ) = x_pre)) (PreH2 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap 0) = 0)) (PreH3 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH4 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH5 : (reaches <= INT_MAX)) (PreH6 : (j <= INT_MAX)) (PreH7 : (count <= INT_MAX)) (PreH8 : (old <= INT_MAX)) (PreH9 : (segments <= INT_MAX)) (PreH10 : (v <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (reaches >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (count >= INT_MIN)) (PreH16 : (old >= INT_MIN)) (PreH17 : (segments >= INT_MIN)) (PreH18 : (v >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH22 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH23 : (j < old)) (PreH24 : (n_pre = (Zlength (values)))) (PreH25 : (2 <= x_pre)) (PreH26 : (x_pre <= 100000)) (PreH27 : (1 <= (Zlength (values)))) (PreH28 : ((Zlength (values)) <= 100000)) (PreH29 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH30 : (Pre x_pre values )) (PreH31 : (0 <= i)) (PreH32 : (i < n_pre)) (PreH33 : (v = (Znth i values 0))) (PreH34 : (1 <= v)) (PreH35 : (v <= x_pre)) (PreH36 : ((x_pre % ( v ) ) = 0)) (PreH37 : (1 <= segments)) (PreH38 : (segments <= (i + 1 ))) (PreH39 : (old = (Zlength (base_products)))) (PreH40 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH41 : (1 <= old)) (PreH42 : (old <= count)) (PreH43 : (count <= x_pre)) (PreH44 : (0 <= j)) (PreH45 : (j <= old)) (PreH46 : (count = (Zlength (products_before_append)))) (PreH47 : (reaches = 0)) (PreH48 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH49 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH50 : (ValuableOuterState x_pre values i segments base_products )) (PreH51 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH52 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH53 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH54 : (ValuableBitmap x_pre products_before_append bitmap )),
  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.seg products_buf 0 (count + 1 ) (app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * v )) ((@nil Z))))) )
  **  (IntArray.undef_seg products_buf (count + 1 ) (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) (replace_Znth (((Znth (j - 0 ) products_before_append 0) * v )) (1) (bitmap)) )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> 1)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "used" ) )) # Ptr  |-> used)
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_35 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : (((Znth (j - 0 ) products_before_append 0) * v ) = x_pre)) (PreH2 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap 0) <> 0)) (PreH3 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH4 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH5 : (reaches <= INT_MAX)) (PreH6 : (j <= INT_MAX)) (PreH7 : (count <= INT_MAX)) (PreH8 : (old <= INT_MAX)) (PreH9 : (segments <= INT_MAX)) (PreH10 : (v <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (reaches >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (count >= INT_MIN)) (PreH16 : (old >= INT_MIN)) (PreH17 : (segments >= INT_MIN)) (PreH18 : (v >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH22 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH23 : (j < old)) (PreH24 : (n_pre = (Zlength (values)))) (PreH25 : (2 <= x_pre)) (PreH26 : (x_pre <= 100000)) (PreH27 : (1 <= (Zlength (values)))) (PreH28 : ((Zlength (values)) <= 100000)) (PreH29 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH30 : (Pre x_pre values )) (PreH31 : (0 <= i)) (PreH32 : (i < n_pre)) (PreH33 : (v = (Znth i values 0))) (PreH34 : (1 <= v)) (PreH35 : (v <= x_pre)) (PreH36 : ((x_pre % ( v ) ) = 0)) (PreH37 : (1 <= segments)) (PreH38 : (segments <= (i + 1 ))) (PreH39 : (old = (Zlength (base_products)))) (PreH40 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH41 : (1 <= old)) (PreH42 : (old <= count)) (PreH43 : (count <= x_pre)) (PreH44 : (0 <= j)) (PreH45 : (j <= old)) (PreH46 : (count = (Zlength (products_before_append)))) (PreH47 : (reaches = 1)) (PreH48 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH49 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH50 : (ValuableOuterState x_pre values i segments base_products )) (PreH51 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH52 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH53 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH54 : (ValuableBitmap x_pre products_before_append bitmap )),
  (UCharArray.full used (x_pre + 1 ) bitmap )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> 1)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_36 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : (((Znth (j - 0 ) products_before_append 0) * v ) = x_pre)) (PreH2 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap 0) <> 0)) (PreH3 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH4 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH5 : (reaches <= INT_MAX)) (PreH6 : (j <= INT_MAX)) (PreH7 : (count <= INT_MAX)) (PreH8 : (old <= INT_MAX)) (PreH9 : (segments <= INT_MAX)) (PreH10 : (v <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (reaches >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (count >= INT_MIN)) (PreH16 : (old >= INT_MIN)) (PreH17 : (segments >= INT_MIN)) (PreH18 : (v >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH22 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH23 : (j < old)) (PreH24 : (n_pre = (Zlength (values)))) (PreH25 : (2 <= x_pre)) (PreH26 : (x_pre <= 100000)) (PreH27 : (1 <= (Zlength (values)))) (PreH28 : ((Zlength (values)) <= 100000)) (PreH29 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH30 : (Pre x_pre values )) (PreH31 : (0 <= i)) (PreH32 : (i < n_pre)) (PreH33 : (v = (Znth i values 0))) (PreH34 : (1 <= v)) (PreH35 : (v <= x_pre)) (PreH36 : ((x_pre % ( v ) ) = 0)) (PreH37 : (1 <= segments)) (PreH38 : (segments <= (i + 1 ))) (PreH39 : (old = (Zlength (base_products)))) (PreH40 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH41 : (1 <= old)) (PreH42 : (old <= count)) (PreH43 : (count <= x_pre)) (PreH44 : (0 <= j)) (PreH45 : (j <= old)) (PreH46 : (count = (Zlength (products_before_append)))) (PreH47 : (reaches = 0)) (PreH48 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH49 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH50 : (ValuableOuterState x_pre values i segments base_products )) (PreH51 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH52 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH53 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH54 : (ValuableBitmap x_pre products_before_append bitmap )),
  (UCharArray.full used (x_pre + 1 ) bitmap )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> 1)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_37 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : (((Znth (j - 0 ) products_before_append 0) * v ) <> x_pre)) (PreH2 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap 0) = 0)) (PreH3 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH4 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH5 : (reaches <= INT_MAX)) (PreH6 : (j <= INT_MAX)) (PreH7 : (count <= INT_MAX)) (PreH8 : (old <= INT_MAX)) (PreH9 : (segments <= INT_MAX)) (PreH10 : (v <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (reaches >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (count >= INT_MIN)) (PreH16 : (old >= INT_MIN)) (PreH17 : (segments >= INT_MIN)) (PreH18 : (v >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH22 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH23 : (j < old)) (PreH24 : (n_pre = (Zlength (values)))) (PreH25 : (2 <= x_pre)) (PreH26 : (x_pre <= 100000)) (PreH27 : (1 <= (Zlength (values)))) (PreH28 : ((Zlength (values)) <= 100000)) (PreH29 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH30 : (Pre x_pre values )) (PreH31 : (0 <= i)) (PreH32 : (i < n_pre)) (PreH33 : (v = (Znth i values 0))) (PreH34 : (1 <= v)) (PreH35 : (v <= x_pre)) (PreH36 : ((x_pre % ( v ) ) = 0)) (PreH37 : (1 <= segments)) (PreH38 : (segments <= (i + 1 ))) (PreH39 : (old = (Zlength (base_products)))) (PreH40 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH41 : (1 <= old)) (PreH42 : (old <= count)) (PreH43 : (count <= x_pre)) (PreH44 : (0 <= j)) (PreH45 : (j <= old)) (PreH46 : (count = (Zlength (products_before_append)))) (PreH47 : (reaches = 1)) (PreH48 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH49 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH50 : (ValuableOuterState x_pre values i segments base_products )) (PreH51 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH52 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH53 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH54 : (ValuableBitmap x_pre products_before_append bitmap )),
  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.seg products_buf 0 (count + 1 ) (app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * v )) ((@nil Z))))) )
  **  (IntArray.undef_seg products_buf (count + 1 ) (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) (replace_Znth (((Znth (j - 0 ) products_before_append 0) * v )) (1) (bitmap)) )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "used" ) )) # Ptr  |-> used)
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_38 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : (((Znth (j - 0 ) products_before_append 0) * v ) <> x_pre)) (PreH2 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap 0) = 0)) (PreH3 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH4 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH5 : (reaches <= INT_MAX)) (PreH6 : (j <= INT_MAX)) (PreH7 : (count <= INT_MAX)) (PreH8 : (old <= INT_MAX)) (PreH9 : (segments <= INT_MAX)) (PreH10 : (v <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (reaches >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (count >= INT_MIN)) (PreH16 : (old >= INT_MIN)) (PreH17 : (segments >= INT_MIN)) (PreH18 : (v >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH22 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH23 : (j < old)) (PreH24 : (n_pre = (Zlength (values)))) (PreH25 : (2 <= x_pre)) (PreH26 : (x_pre <= 100000)) (PreH27 : (1 <= (Zlength (values)))) (PreH28 : ((Zlength (values)) <= 100000)) (PreH29 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH30 : (Pre x_pre values )) (PreH31 : (0 <= i)) (PreH32 : (i < n_pre)) (PreH33 : (v = (Znth i values 0))) (PreH34 : (1 <= v)) (PreH35 : (v <= x_pre)) (PreH36 : ((x_pre % ( v ) ) = 0)) (PreH37 : (1 <= segments)) (PreH38 : (segments <= (i + 1 ))) (PreH39 : (old = (Zlength (base_products)))) (PreH40 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH41 : (1 <= old)) (PreH42 : (old <= count)) (PreH43 : (count <= x_pre)) (PreH44 : (0 <= j)) (PreH45 : (j <= old)) (PreH46 : (count = (Zlength (products_before_append)))) (PreH47 : (reaches = 0)) (PreH48 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH49 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH50 : (ValuableOuterState x_pre values i segments base_products )) (PreH51 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH52 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH53 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH54 : (ValuableBitmap x_pre products_before_append bitmap )),
  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.seg products_buf 0 (count + 1 ) (app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * v )) ((@nil Z))))) )
  **  (IntArray.undef_seg products_buf (count + 1 ) (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) (replace_Znth (((Znth (j - 0 ) products_before_append 0) * v )) (1) (bitmap)) )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "used" ) )) # Ptr  |-> used)
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_39 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : (((Znth (j - 0 ) products_before_append 0) * v ) <> x_pre)) (PreH2 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap 0) <> 0)) (PreH3 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH4 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH5 : (reaches <= INT_MAX)) (PreH6 : (j <= INT_MAX)) (PreH7 : (count <= INT_MAX)) (PreH8 : (old <= INT_MAX)) (PreH9 : (segments <= INT_MAX)) (PreH10 : (v <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (reaches >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (count >= INT_MIN)) (PreH16 : (old >= INT_MIN)) (PreH17 : (segments >= INT_MIN)) (PreH18 : (v >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH22 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH23 : (j < old)) (PreH24 : (n_pre = (Zlength (values)))) (PreH25 : (2 <= x_pre)) (PreH26 : (x_pre <= 100000)) (PreH27 : (1 <= (Zlength (values)))) (PreH28 : ((Zlength (values)) <= 100000)) (PreH29 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH30 : (Pre x_pre values )) (PreH31 : (0 <= i)) (PreH32 : (i < n_pre)) (PreH33 : (v = (Znth i values 0))) (PreH34 : (1 <= v)) (PreH35 : (v <= x_pre)) (PreH36 : ((x_pre % ( v ) ) = 0)) (PreH37 : (1 <= segments)) (PreH38 : (segments <= (i + 1 ))) (PreH39 : (old = (Zlength (base_products)))) (PreH40 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH41 : (1 <= old)) (PreH42 : (old <= count)) (PreH43 : (count <= x_pre)) (PreH44 : (0 <= j)) (PreH45 : (j <= old)) (PreH46 : (count = (Zlength (products_before_append)))) (PreH47 : (reaches = 1)) (PreH48 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH49 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH50 : (ValuableOuterState x_pre values i segments base_products )) (PreH51 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH52 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH53 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH54 : (ValuableBitmap x_pre products_before_append bitmap )),
  (UCharArray.full used (x_pre + 1 ) bitmap )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_40 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : (((Znth (j - 0 ) products_before_append 0) * v ) <> x_pre)) (PreH2 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap 0) <> 0)) (PreH3 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH4 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH5 : (reaches <= INT_MAX)) (PreH6 : (j <= INT_MAX)) (PreH7 : (count <= INT_MAX)) (PreH8 : (old <= INT_MAX)) (PreH9 : (segments <= INT_MAX)) (PreH10 : (v <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (reaches >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (count >= INT_MIN)) (PreH16 : (old >= INT_MIN)) (PreH17 : (segments >= INT_MIN)) (PreH18 : (v >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH22 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH23 : (j < old)) (PreH24 : (n_pre = (Zlength (values)))) (PreH25 : (2 <= x_pre)) (PreH26 : (x_pre <= 100000)) (PreH27 : (1 <= (Zlength (values)))) (PreH28 : ((Zlength (values)) <= 100000)) (PreH29 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH30 : (Pre x_pre values )) (PreH31 : (0 <= i)) (PreH32 : (i < n_pre)) (PreH33 : (v = (Znth i values 0))) (PreH34 : (1 <= v)) (PreH35 : (v <= x_pre)) (PreH36 : ((x_pre % ( v ) ) = 0)) (PreH37 : (1 <= segments)) (PreH38 : (segments <= (i + 1 ))) (PreH39 : (old = (Zlength (base_products)))) (PreH40 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH41 : (1 <= old)) (PreH42 : (old <= count)) (PreH43 : (count <= x_pre)) (PreH44 : (0 <= j)) (PreH45 : (j <= old)) (PreH46 : (count = (Zlength (products_before_append)))) (PreH47 : (reaches = 0)) (PreH48 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH49 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH50 : (ValuableOuterState x_pre values i segments base_products )) (PreH51 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH52 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH53 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH54 : (ValuableBitmap x_pre products_before_append bitmap )),
  (UCharArray.full used (x_pre + 1 ) bitmap )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_41 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((Znth (j - 0 ) products_before_append 0) > (x_pre ÷ v ))) (PreH2 : (j < old)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 100000)) (PreH6 : (1 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH9 : (Pre x_pre values )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (v = (Znth i values 0))) (PreH13 : (1 <= v)) (PreH14 : (v <= x_pre)) (PreH15 : ((x_pre % ( v ) ) = 0)) (PreH16 : (1 <= segments)) (PreH17 : (segments <= (i + 1 ))) (PreH18 : (old = (Zlength (base_products)))) (PreH19 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH20 : (1 <= old)) (PreH21 : (old <= count)) (PreH22 : (count <= x_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= old)) (PreH25 : (count = (Zlength (products_before_append)))) (PreH26 : (reaches = 0)) (PreH27 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH28 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH29 : (ValuableOuterState x_pre values i segments base_products )) (PreH30 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH31 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH32 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH33 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_42 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((Znth (j - 0 ) products_before_append 0) > (x_pre ÷ v ))) (PreH2 : (j < old)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 100000)) (PreH6 : (1 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH9 : (Pre x_pre values )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (v = (Znth i values 0))) (PreH13 : (1 <= v)) (PreH14 : (v <= x_pre)) (PreH15 : ((x_pre % ( v ) ) = 0)) (PreH16 : (1 <= segments)) (PreH17 : (segments <= (i + 1 ))) (PreH18 : (old = (Zlength (base_products)))) (PreH19 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH20 : (1 <= old)) (PreH21 : (old <= count)) (PreH22 : (count <= x_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= old)) (PreH25 : (count = (Zlength (products_before_append)))) (PreH26 : (reaches = 1)) (PreH27 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH28 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH29 : (ValuableOuterState x_pre values i segments base_products )) (PreH30 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH31 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH32 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH33 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_43 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) <> 0)) (PreH2 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH3 : (j < old)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 100000)) (PreH7 : (1 <= (Zlength (values)))) (PreH8 : ((Zlength (values)) <= 100000)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH10 : (Pre x_pre values )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (v = (Znth i values 0))) (PreH14 : (1 <= v)) (PreH15 : (v <= x_pre)) (PreH16 : ((x_pre % ( v ) ) = 0)) (PreH17 : (1 <= segments)) (PreH18 : (segments <= (i + 1 ))) (PreH19 : (old = (Zlength (base_products)))) (PreH20 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH21 : (1 <= old)) (PreH22 : (old <= count)) (PreH23 : (count <= x_pre)) (PreH24 : (0 <= j)) (PreH25 : (j <= old)) (PreH26 : (count = (Zlength (products_before_append)))) (PreH27 : (reaches = 1)) (PreH28 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH29 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH30 : (ValuableOuterState x_pre values i segments base_products )) (PreH31 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH32 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH33 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH34 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_44 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) <> 0)) (PreH2 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH3 : (j < old)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 100000)) (PreH7 : (1 <= (Zlength (values)))) (PreH8 : ((Zlength (values)) <= 100000)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH10 : (Pre x_pre values )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (v = (Znth i values 0))) (PreH14 : (1 <= v)) (PreH15 : (v <= x_pre)) (PreH16 : ((x_pre % ( v ) ) = 0)) (PreH17 : (1 <= segments)) (PreH18 : (segments <= (i + 1 ))) (PreH19 : (old = (Zlength (base_products)))) (PreH20 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH21 : (1 <= old)) (PreH22 : (old <= count)) (PreH23 : (count <= x_pre)) (PreH24 : (0 <= j)) (PreH25 : (j <= old)) (PreH26 : (count = (Zlength (products_before_append)))) (PreH27 : (reaches = 0)) (PreH28 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH29 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH30 : (ValuableOuterState x_pre values i segments base_products )) (PreH31 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH32 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH33 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH34 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_45 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (products: (@list Z)) (bitmap: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (products_buf: Z) (used: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH7 : (Pre x_pre values )) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (v = (Znth i values 0))) (PreH11 : (1 <= v)) (PreH12 : (v <= x_pre)) (PreH13 : ((x_pre % ( v ) ) = 0)) (PreH14 : (1 <= segments)) (PreH15 : (segments <= (i + 1 ))) (PreH16 : (old = (Zlength (base_products)))) (PreH17 : (base_products = (sublist (0) (old) (products)))) (PreH18 : (1 <= old)) (PreH19 : (old <= count)) (PreH20 : (count <= x_pre)) (PreH21 : (count = (Zlength (products)))) (PreH22 : (reaches = 1)) (PreH23 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH24 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre)))) (PreH25 : (ValuableOuterState x_pre values i segments base_products )) (PreH26 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH27 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH28 : (ValuableClosureState x_pre segment v base_products old products reaches )) (PreH29 : (ValuableBitmap x_pre products bitmap )) (PreH30 : (reaches = 0)),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ False ”
.

Definition solver_safety_wit_46 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (products: (@list Z)) (bitmap: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (products_buf: Z) (used: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH7 : (Pre x_pre values )) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (v = (Znth i values 0))) (PreH11 : (1 <= v)) (PreH12 : (v <= x_pre)) (PreH13 : ((x_pre % ( v ) ) = 0)) (PreH14 : (1 <= segments)) (PreH15 : (segments <= (i + 1 ))) (PreH16 : (old = (Zlength (base_products)))) (PreH17 : (base_products = (sublist (0) (old) (products)))) (PreH18 : (1 <= old)) (PreH19 : (old <= count)) (PreH20 : (count <= x_pre)) (PreH21 : (count = (Zlength (products)))) (PreH22 : (reaches = 0)) (PreH23 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH24 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre)))) (PreH25 : (ValuableOuterState x_pre values i segments base_products )) (PreH26 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH27 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH28 : (ValuableClosureState x_pre segment v base_products old products reaches )) (PreH29 : (ValuableBitmap x_pre products bitmap )) (PreH30 : (reaches <> 0)),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ False ”
.

Definition solver_safety_wit_47 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (products: (@list Z)) (bitmap: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (products_buf: Z) (used: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH7 : (Pre x_pre values )) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (v = (Znth i values 0))) (PreH11 : (1 <= v)) (PreH12 : (v <= x_pre)) (PreH13 : ((x_pre % ( v ) ) = 0)) (PreH14 : (1 <= segments)) (PreH15 : (segments <= (i + 1 ))) (PreH16 : (old = (Zlength (base_products)))) (PreH17 : (base_products = (sublist (0) (old) (products)))) (PreH18 : (1 <= old)) (PreH19 : (old <= count)) (PreH20 : (count <= x_pre)) (PreH21 : (count = (Zlength (products)))) (PreH22 : (reaches = 1)) (PreH23 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH24 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre)))) (PreH25 : (ValuableOuterState x_pre values i segments base_products )) (PreH26 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH27 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH28 : (ValuableClosureState x_pre segment v base_products old products reaches )) (PreH29 : (ValuableBitmap x_pre products bitmap )) (PreH30 : (reaches <> 0)),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ ((segments + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (segments + 1 )) ”
.

Definition solver_safety_wit_48 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (products: (@list Z)) (bitmap: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (products_buf: Z) (used: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH7 : (Pre x_pre values )) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (v = (Znth i values 0))) (PreH11 : (1 <= v)) (PreH12 : (v <= x_pre)) (PreH13 : ((x_pre % ( v ) ) = 0)) (PreH14 : (1 <= segments)) (PreH15 : (segments <= (i + 1 ))) (PreH16 : (old = (Zlength (base_products)))) (PreH17 : (base_products = (sublist (0) (old) (products)))) (PreH18 : (1 <= old)) (PreH19 : (old <= count)) (PreH20 : (count <= x_pre)) (PreH21 : (count = (Zlength (products)))) (PreH22 : (reaches = 1)) (PreH23 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH24 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre)))) (PreH25 : (ValuableOuterState x_pre values i segments base_products )) (PreH26 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH27 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH28 : (ValuableClosureState x_pre segment v base_products old products reaches )) (PreH29 : (ValuableBitmap x_pre products bitmap )) (PreH30 : (reaches <> 0)),
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> (segments + 1 ))
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_49 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (products: (@list Z)) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (PreH1 : (j < count)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (v = (Znth i values 0))) (PreH12 : (1 <= v)) (PreH13 : (v <= x_pre)) (PreH14 : ((x_pre % ( v ) ) = 0)) (PreH15 : (2 <= segments)) (PreH16 : (segments <= (i + 2 ))) (PreH17 : (old = (Zlength (base_products)))) (PreH18 : (base_products = (sublist (0) (old) (products)))) (PreH19 : (count = (Zlength (products)))) (PreH20 : (1 <= count)) (PreH21 : (count <= x_pre)) (PreH22 : (0 <= j)) (PreH23 : (j <= count)) (PreH24 : (reaches = 1)) (PreH25 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH26 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre)))) (PreH27 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH28 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH29 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH30 : (ValuableClosureState x_pre segment v base_products old products 1 )) (PreH31 : (ValuableClearingState x_pre products j bitmap )),
  (UCharArray.full used (x_pre + 1 ) (replace_Znth ((Znth (j - 0 ) products 0)) (0) (bitmap)) )
  **  (IntArray.seg products_buf 0 count products )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_50 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (products: (@list Z)) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (PreH1 : (j < count)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (v = (Znth i values 0))) (PreH12 : (1 <= v)) (PreH13 : (v <= x_pre)) (PreH14 : ((x_pre % ( v ) ) = 0)) (PreH15 : (2 <= segments)) (PreH16 : (segments <= (i + 2 ))) (PreH17 : (old = (Zlength (base_products)))) (PreH18 : (base_products = (sublist (0) (old) (products)))) (PreH19 : (count = (Zlength (products)))) (PreH20 : (1 <= count)) (PreH21 : (count <= x_pre)) (PreH22 : (0 <= j)) (PreH23 : (j <= count)) (PreH24 : (reaches = 1)) (PreH25 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH26 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre)))) (PreH27 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH28 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH29 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH30 : (ValuableClosureState x_pre segment v base_products old products 1 )) (PreH31 : (ValuableClearingState x_pre products j bitmap )),
  (IntArray.seg products_buf 0 count products )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_51 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (products: (@list Z)) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (PreH1 : (j >= count)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (v = (Znth i values 0))) (PreH12 : (1 <= v)) (PreH13 : (v <= x_pre)) (PreH14 : ((x_pre % ( v ) ) = 0)) (PreH15 : (2 <= segments)) (PreH16 : (segments <= (i + 2 ))) (PreH17 : (old = (Zlength (base_products)))) (PreH18 : (base_products = (sublist (0) (old) (products)))) (PreH19 : (count = (Zlength (products)))) (PreH20 : (1 <= count)) (PreH21 : (count <= x_pre)) (PreH22 : (0 <= j)) (PreH23 : (j <= count)) (PreH24 : (reaches = 1)) (PreH25 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH26 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre)))) (PreH27 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH28 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH29 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH30 : (ValuableClosureState x_pre segment v base_products old products 1 )) (PreH31 : (ValuableClearingState x_pre products j bitmap )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_52 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (products: (@list Z)) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (PreH1 : (j >= count)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (v = (Znth i values 0))) (PreH12 : (1 <= v)) (PreH13 : (v <= x_pre)) (PreH14 : ((x_pre % ( v ) ) = 0)) (PreH15 : (2 <= segments)) (PreH16 : (segments <= (i + 2 ))) (PreH17 : (old = (Zlength (base_products)))) (PreH18 : (base_products = (sublist (0) (old) (products)))) (PreH19 : (count = (Zlength (products)))) (PreH20 : (1 <= count)) (PreH21 : (count <= x_pre)) (PreH22 : (0 <= j)) (PreH23 : (j <= count)) (PreH24 : (reaches = 1)) (PreH25 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH26 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre)))) (PreH27 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH28 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH29 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH30 : (ValuableClosureState x_pre segment v base_products old products 1 )) (PreH31 : (ValuableClearingState x_pre products j bitmap )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> 1)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_53 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (products: (@list Z)) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (PreH1 : (j >= count)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (v = (Znth i values 0))) (PreH12 : (1 <= v)) (PreH13 : (v <= x_pre)) (PreH14 : ((x_pre % ( v ) ) = 0)) (PreH15 : (2 <= segments)) (PreH16 : (segments <= (i + 2 ))) (PreH17 : (old = (Zlength (base_products)))) (PreH18 : (base_products = (sublist (0) (old) (products)))) (PreH19 : (count = (Zlength (products)))) (PreH20 : (1 <= count)) (PreH21 : (count <= x_pre)) (PreH22 : (0 <= j)) (PreH23 : (j <= count)) (PreH24 : (reaches = 1)) (PreH25 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH26 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre)))) (PreH27 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH28 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH29 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH30 : (ValuableClosureState x_pre segment v base_products old products 1 )) (PreH31 : (ValuableClearingState x_pre products j bitmap )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> 1)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_54 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (products: (@list Z)) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (PreH1 : (j >= count)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (v = (Znth i values 0))) (PreH12 : (1 <= v)) (PreH13 : (v <= x_pre)) (PreH14 : ((x_pre % ( v ) ) = 0)) (PreH15 : (2 <= segments)) (PreH16 : (segments <= (i + 2 ))) (PreH17 : (old = (Zlength (base_products)))) (PreH18 : (base_products = (sublist (0) (old) (products)))) (PreH19 : (count = (Zlength (products)))) (PreH20 : (1 <= count)) (PreH21 : (count <= x_pre)) (PreH22 : (0 <= j)) (PreH23 : (j <= count)) (PreH24 : (reaches = 1)) (PreH25 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH26 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre)))) (PreH27 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH28 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH29 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH30 : (ValuableClosureState x_pre segment v base_products old products 1 )) (PreH31 : (ValuableClearingState x_pre products j bitmap )),
  (IntArray.full products_buf count (replace_Znth (0) (1) (products)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> 1)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_55 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (products: (@list Z)) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (PreH1 : (j >= count)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (v = (Znth i values 0))) (PreH12 : (1 <= v)) (PreH13 : (v <= x_pre)) (PreH14 : ((x_pre % ( v ) ) = 0)) (PreH15 : (2 <= segments)) (PreH16 : (segments <= (i + 2 ))) (PreH17 : (old = (Zlength (base_products)))) (PreH18 : (base_products = (sublist (0) (old) (products)))) (PreH19 : (count = (Zlength (products)))) (PreH20 : (1 <= count)) (PreH21 : (count <= x_pre)) (PreH22 : (0 <= j)) (PreH23 : (j <= count)) (PreH24 : (reaches = 1)) (PreH25 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH26 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre)))) (PreH27 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH28 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH29 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH30 : (ValuableClosureState x_pre segment v base_products old products 1 )) (PreH31 : (ValuableClearingState x_pre products j bitmap )),
  (IntArray.full products_buf count (replace_Znth (0) (1) (products)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> 1)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_56 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (old_products: (@list Z)) (bitmap: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (products_buf: Z) (used: Z) (PreH1 : ((Znth v bitmap 0) = 0)) (PreH2 : (0 <= v)) (PreH3 : (v < (x_pre + 1 ))) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (count <= INT_MAX)) (PreH6 : (old <= INT_MAX)) (PreH7 : (segments <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (reaches >= INT_MIN)) (PreH11 : (count >= INT_MIN)) (PreH12 : (old >= INT_MIN)) (PreH13 : (segments >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (2 <= x_pre)) (PreH18 : (x_pre <= 100000)) (PreH19 : (1 <= (Zlength (values)))) (PreH20 : ((Zlength (values)) <= 100000)) (PreH21 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH22 : (Pre x_pre values )) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (v = (Znth i values 0))) (PreH26 : (1 <= v)) (PreH27 : (v <= x_pre)) (PreH28 : ((x_pre % ( v ) ) = 0)) (PreH29 : (2 <= segments)) (PreH30 : (segments <= (i + 2 ))) (PreH31 : (old = (Zlength (base_products)))) (PreH32 : (base_products = (sublist (0) (old) (old_products)))) (PreH33 : (count = 1)) (PreH34 : (1 <= count)) (PreH35 : (count <= x_pre)) (PreH36 : (reaches = 1)) (PreH37 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH38 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH39 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH40 : (ValuableClosureState x_pre segment v base_products old old_products 1 )) (PreH41 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH42 : (ValuableBitmap x_pre (cons (1) ((@nil Z))) bitmap )),
  (UCharArray.full used (x_pre + 1 ) bitmap )
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.seg products_buf 0 count (cons (1) ((@nil Z))) )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_57 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (old_products: (@list Z)) (bitmap: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (products_buf: Z) (used: Z) (PreH1 : ((Znth v bitmap 0) = 0)) (PreH2 : (0 <= v)) (PreH3 : (v < (x_pre + 1 ))) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (count <= INT_MAX)) (PreH6 : (old <= INT_MAX)) (PreH7 : (segments <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (reaches >= INT_MIN)) (PreH11 : (count >= INT_MIN)) (PreH12 : (old >= INT_MIN)) (PreH13 : (segments >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (2 <= x_pre)) (PreH18 : (x_pre <= 100000)) (PreH19 : (1 <= (Zlength (values)))) (PreH20 : ((Zlength (values)) <= 100000)) (PreH21 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH22 : (Pre x_pre values )) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (v = (Znth i values 0))) (PreH26 : (1 <= v)) (PreH27 : (v <= x_pre)) (PreH28 : ((x_pre % ( v ) ) = 0)) (PreH29 : (2 <= segments)) (PreH30 : (segments <= (i + 2 ))) (PreH31 : (old = (Zlength (base_products)))) (PreH32 : (base_products = (sublist (0) (old) (old_products)))) (PreH33 : (count = 1)) (PreH34 : (1 <= count)) (PreH35 : (count <= x_pre)) (PreH36 : (reaches = 1)) (PreH37 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH38 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH39 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH40 : (ValuableClosureState x_pre segment v base_products old old_products 1 )) (PreH41 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH42 : (ValuableBitmap x_pre (cons (1) ((@nil Z))) bitmap )),
  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.seg products_buf 0 (count + 1 ) (cons (1) ((cons (v) ((@nil Z))))) )
  **  (IntArray.undef_seg products_buf (count + 1 ) (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) (replace_Znth (v) (1) (bitmap)) )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "used" ) )) # Ptr  |-> used)
|--
  “ ((count + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition solver_safety_wit_58 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (old_products: (@list Z)) (bitmap: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (products_buf: Z) (used: Z) (PreH1 : ((Znth v bitmap 0) = 0)) (PreH2 : (0 <= v)) (PreH3 : (v < (x_pre + 1 ))) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (count <= INT_MAX)) (PreH6 : (old <= INT_MAX)) (PreH7 : (segments <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (reaches >= INT_MIN)) (PreH11 : (count >= INT_MIN)) (PreH12 : (old >= INT_MIN)) (PreH13 : (segments >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (2 <= x_pre)) (PreH18 : (x_pre <= 100000)) (PreH19 : (1 <= (Zlength (values)))) (PreH20 : ((Zlength (values)) <= 100000)) (PreH21 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH22 : (Pre x_pre values )) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (v = (Znth i values 0))) (PreH26 : (1 <= v)) (PreH27 : (v <= x_pre)) (PreH28 : ((x_pre % ( v ) ) = 0)) (PreH29 : (2 <= segments)) (PreH30 : (segments <= (i + 2 ))) (PreH31 : (old = (Zlength (base_products)))) (PreH32 : (base_products = (sublist (0) (old) (old_products)))) (PreH33 : (count = 1)) (PreH34 : (1 <= count)) (PreH35 : (count <= x_pre)) (PreH36 : (reaches = 1)) (PreH37 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH38 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH39 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH40 : (ValuableClosureState x_pre segment v base_products old old_products 1 )) (PreH41 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH42 : (ValuableBitmap x_pre (cons (1) ((@nil Z))) bitmap )),
  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.seg products_buf 0 (count + 1 ) (cons (1) ((cons (v) ((@nil Z))))) )
  **  (IntArray.undef_seg products_buf (count + 1 ) (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) (replace_Znth (v) (1) (bitmap)) )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "used" ) )) # Ptr  |-> used)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_59 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (old_products: (@list Z)) (bitmap: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (products_buf: Z) (used: Z) (PreH1 : ((Znth v bitmap 0) <> 0)) (PreH2 : (0 <= v)) (PreH3 : (v < (x_pre + 1 ))) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (count <= INT_MAX)) (PreH6 : (old <= INT_MAX)) (PreH7 : (segments <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (reaches >= INT_MIN)) (PreH11 : (count >= INT_MIN)) (PreH12 : (old >= INT_MIN)) (PreH13 : (segments >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (2 <= x_pre)) (PreH18 : (x_pre <= 100000)) (PreH19 : (1 <= (Zlength (values)))) (PreH20 : ((Zlength (values)) <= 100000)) (PreH21 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH22 : (Pre x_pre values )) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (v = (Znth i values 0))) (PreH26 : (1 <= v)) (PreH27 : (v <= x_pre)) (PreH28 : ((x_pre % ( v ) ) = 0)) (PreH29 : (2 <= segments)) (PreH30 : (segments <= (i + 2 ))) (PreH31 : (old = (Zlength (base_products)))) (PreH32 : (base_products = (sublist (0) (old) (old_products)))) (PreH33 : (count = 1)) (PreH34 : (1 <= count)) (PreH35 : (count <= x_pre)) (PreH36 : (reaches = 1)) (PreH37 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH38 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH39 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH40 : (ValuableClosureState x_pre segment v base_products old old_products 1 )) (PreH41 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH42 : (ValuableBitmap x_pre (cons (1) ((@nil Z))) bitmap )),
  (UCharArray.full used (x_pre + 1 ) bitmap )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.seg products_buf 0 count (cons (1) ((@nil Z))) )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_60 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (products: (@list Z)) (bitmap: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (products_buf: Z) (used: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH7 : (Pre x_pre values )) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (v = (Znth i values 0))) (PreH11 : (1 <= v)) (PreH12 : (v <= x_pre)) (PreH13 : ((x_pre % ( v ) ) = 0)) (PreH14 : (1 <= segments)) (PreH15 : (segments <= (i + 1 ))) (PreH16 : (old = (Zlength (base_products)))) (PreH17 : (base_products = (sublist (0) (old) (products)))) (PreH18 : (1 <= old)) (PreH19 : (old <= count)) (PreH20 : (count <= x_pre)) (PreH21 : (count = (Zlength (products)))) (PreH22 : (reaches = 0)) (PreH23 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH24 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre)))) (PreH25 : (ValuableOuterState x_pre values i segments base_products )) (PreH26 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH27 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH28 : (ValuableClosureState x_pre segment v base_products old products reaches )) (PreH29 : (ValuableBitmap x_pre products bitmap )) (PreH30 : (reaches = 0)),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_61 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (bitmap: (@list Z)) (products: (@list Z)) (count: Z) (segments: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= segments)) (PreH12 : (segments <= (i + 1 ))) (PreH13 : (count = (Zlength (products)))) (PreH14 : (1 <= count)) (PreH15 : (count <= x_pre)) (PreH16 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH17 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre)))) (PreH18 : (ValuableOuterState x_pre values i segments products )) (PreH19 : (ValuableForcedHistory x_pre values i segments products )) (PreH20 : (ValuableAlignedHistory x_pre values i segments products )) (PreH21 : (ValuableBitmap x_pre products bitmap )) (PreH22 : ((x_pre % ( (Znth i values 0) ) ) <> 0)),
  (IntArray.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (n_pre = (Zlength (values)))),
  (UCharArray.full retval (x_pre + 1 ) (replace_Znth (1) (1) ((repeat_Z (0) ((x_pre + 1 ))))) )
  **  (((retval_2 + (0 * sizeof(INT)))) # Int  |-> 1)
  **  (IntArray.undef_seg retval_2 1 (x_pre + 1 ) )
  **  (IntArray.full a_pre n_pre values )
|--
  EX (bitmap: (@list Z)) (products: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= (0 + 1 )) ”
  &&  “ (1 = (Zlength (products))) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= x_pre) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < 1)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values 0 1 products ) ”
  &&  “ (ValuableForcedHistory x_pre values 0 1 products ) ”
  &&  “ (ValuableAlignedHistory x_pre values 0 1 products ) ”
  &&  “ (ValuableBitmap x_pre products bitmap ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg retval_2 0 1 products )
  **  (IntArray.undef_seg retval_2 1 (x_pre + 1 ) )
  **  (UCharArray.full retval (x_pre + 1 ) bitmap )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : (1 >= INT_MIN)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 100000)) (PreH7 : (1 <= (Zlength (values)))) (PreH8 : ((Zlength (values)) <= 100000)) (PreH9 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 200000)))) (PreH10 : (Pre x_pre values )) (PreH11 : (n_pre = (Zlength (values)))),
  (((retval_2 + (0 * sizeof(INT)))) # Int  |-> 1)
|--
  EX (products: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= (0 + 1 )) ”
  &&  “ (1 = (Zlength (products))) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= x_pre) ”
  &&  “ ((Zlength ((replace_Znth (1) (1) ((repeat_Z (0) ((x_pre + 1 ))))))) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < 1)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values 0 1 products ) ”
  &&  “ (ValuableForcedHistory x_pre values 0 1 products ) ”
  &&  “ (ValuableAlignedHistory x_pre values 0 1 products ) ”
  &&  “ (ValuableBitmap x_pre products (replace_Znth (1) (1) ((repeat_Z (0) ((x_pre + 1 ))))) ) ”
  &&  (IntArray.seg retval_2 0 1 products )
).

Definition solver_entail_wit_2 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (bitmap_2: (@list Z)) (products_2: (@list Z)) (count: Z) (segments: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= segments)) (PreH12 : (segments <= (i + 1 ))) (PreH13 : (count = (Zlength (products_2)))) (PreH14 : (1 <= count)) (PreH15 : (count <= x_pre)) (PreH16 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH17 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < count)) -> ((1 <= (Znth k_4 products_2 0)) /\ ((Znth k_4 products_2 0) <= x_pre)))) (PreH18 : (ValuableOuterState x_pre values i segments products_2 )) (PreH19 : (ValuableForcedHistory x_pre values i segments products_2 )) (PreH20 : (ValuableAlignedHistory x_pre values i segments products_2 )) (PreH21 : (ValuableBitmap x_pre products_2 bitmap_2 )) (PreH22 : ((x_pre % ( (Znth i values 0) ) ) = 0)),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products_2 )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap_2 )
|--
  EX (segment: (@list Z)) (bitmap: (@list Z)) (products: (@list Z)) (base_products: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Znth i values 0) = (Znth i values 0)) ”
  &&  “ (1 <= (Znth i values 0)) ”
  &&  “ ((Znth i values 0) <= x_pre) ”
  &&  “ ((x_pre % ( (Znth i values 0) ) ) = 0) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (count = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (count) (products))) ”
  &&  “ (1 <= count) ”
  &&  “ (count <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= count) ”
  &&  “ (count = (Zlength (products))) ”
  &&  “ (0 = 0) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableClosureState x_pre segment (Znth i values 0) base_products 0 products 0 ) ”
  &&  “ (ValuableBitmap x_pre products bitmap ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (bitmap_2: (@list Z)) (products_2: (@list Z)) (count: Z) (segments: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= segments)) (PreH12 : (segments <= (i + 1 ))) (PreH13 : (count = (Zlength (products_2)))) (PreH14 : (1 <= count)) (PreH15 : (count <= x_pre)) (PreH16 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH17 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < count)) -> ((1 <= (Znth k_4 products_2 0)) /\ ((Znth k_4 products_2 0) <= x_pre)))) (PreH18 : (ValuableOuterState x_pre values i segments products_2 )) (PreH19 : (ValuableForcedHistory x_pre values i segments products_2 )) (PreH20 : (ValuableAlignedHistory x_pre values i segments products_2 )) (PreH21 : (ValuableBitmap x_pre products_2 bitmap_2 )) (PreH22 : ((x_pre % ( (Znth i values 0) ) ) = 0)),
  TT && emp 
|--
  EX (segment: (@list Z)),
  “ (1 <= (Znth i values 0)) ”
  &&  “ ((Znth i values 0) <= x_pre) ”
  &&  “ ((Zlength (products_2)) = (Zlength ((sublist (0) ((Zlength (products_2))) (products_2))))) ”
  &&  “ ((Zlength (products_2)) <= (Zlength (products_2))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (Zlength (products_2))) ”
  &&  “ (ValuableOuterState x_pre values i segments (sublist (0) ((Zlength (products_2))) (products_2)) ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments (sublist (0) ((Zlength (products_2))) (products_2)) ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments (sublist (0) ((Zlength (products_2))) (products_2)) ) ”
  &&  “ (ValuableClosureState x_pre segment (Znth i values 0) (sublist (0) ((Zlength (products_2))) (products_2)) 0 products_2 0 ) ”
  &&  emp
).

Definition solver_entail_wit_3_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH2 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH3 : (j < old)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 100000)) (PreH7 : (1 <= (Zlength (values)))) (PreH8 : ((Zlength (values)) <= 100000)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH10 : (Pre x_pre values )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (v = (Znth i values 0))) (PreH14 : (1 <= v)) (PreH15 : (v <= x_pre)) (PreH16 : ((x_pre % ( v ) ) = 0)) (PreH17 : (1 <= segments)) (PreH18 : (segments <= (i + 1 ))) (PreH19 : (old = (Zlength (base_products)))) (PreH20 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH21 : (1 <= old)) (PreH22 : (old <= count)) (PreH23 : (count <= x_pre)) (PreH24 : (0 <= j)) (PreH25 : (j <= old)) (PreH26 : (count = (Zlength (products_before_append)))) (PreH27 : (reaches = 1)) (PreH28 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH29 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH30 : (ValuableOuterState x_pre values i segments base_products )) (PreH31 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH32 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH33 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH34 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "p" ) )) # Int  |-> ((Znth (j - 0 ) products_before_append 0) * v ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  (“ (1 <= ((Znth (j - 0 ) products_before_append 0) * v )) ”
  &&  “ (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre) ”
  &&  “ (reaches <= INT_MAX) ”
  &&  “ (j <= INT_MAX) ”
  &&  “ (count <= INT_MAX) ”
  &&  “ (old <= INT_MAX) ”
  &&  “ (segments <= INT_MAX) ”
  &&  “ (v <= INT_MAX) ”
  &&  “ (i <= INT_MAX) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (reaches >= INT_MIN) ”
  &&  “ (j >= INT_MIN) ”
  &&  “ (count >= INT_MIN) ”
  &&  “ (old >= INT_MIN) ”
  &&  “ (segments >= INT_MIN) ”
  &&  “ (v >= INT_MIN) ”
  &&  “ (i >= INT_MIN) ”
  &&  “ (n_pre >= INT_MIN) ”
  &&  “ ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0) ”
  &&  “ ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v )) ”
  &&  “ (j < old) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products_before_append))) ”
  &&  “ (1 <= old) ”
  &&  “ (old <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= old) ”
  &&  “ (count = (Zlength (products_before_append))) ”
  &&  “ (reaches = 1) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products j products_before_append reaches ) ”
  &&  “ (ValuableBitmap x_pre products_before_append bitmap ) ”
  &&  ((( &( "p" ) )) # Int  |-> ((Znth (j - 0 ) products_before_append 0) * v ))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap ))
  ||
  (EX (used_2: Z) (products_buf_2: Z) (segment_2: (@list Z)) (bitmap_2: (@list Z)) (reaches_2: Z) (j_2: Z) (count_2: Z) (base_products_2: (@list Z)) (old_2: Z) (segments_2: Z) (v_2: Z) (i_2: Z),
  “ (1 <= ((Znth (j_2 - 0 ) products_before_append 0) * v_2 )) ”
  &&  “ (((Znth (j_2 - 0 ) products_before_append 0) * v_2 ) <= x_pre) ”
  &&  “ (reaches_2 <= INT_MAX) ”
  &&  “ (j_2 <= INT_MAX) ”
  &&  “ (count_2 <= INT_MAX) ”
  &&  “ (old_2 <= INT_MAX) ”
  &&  “ (segments_2 <= INT_MAX) ”
  &&  “ (v_2 <= INT_MAX) ”
  &&  “ (i_2 <= INT_MAX) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (reaches_2 >= INT_MIN) ”
  &&  “ (j_2 >= INT_MIN) ”
  &&  “ (count_2 >= INT_MIN) ”
  &&  “ (old_2 >= INT_MIN) ”
  &&  “ (segments_2 >= INT_MIN) ”
  &&  “ (v_2 >= INT_MIN) ”
  &&  “ (i_2 >= INT_MIN) ”
  &&  “ (n_pre >= INT_MIN) ”
  &&  “ ((x_pre % ( ((Znth (j_2 - 0 ) products_before_append 0) * v_2 ) ) ) = 0) ”
  &&  “ ((Znth (j_2 - 0 ) products_before_append 0) <= (x_pre ÷ v_2 )) ”
  &&  “ (j_2 < old_2) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i_2) ”
  &&  “ (i_2 < n_pre) ”
  &&  “ (v_2 = (Znth i_2 values 0)) ”
  &&  “ (1 <= v_2) ”
  &&  “ (v_2 <= x_pre) ”
  &&  “ ((x_pre % ( v_2 ) ) = 0) ”
  &&  “ (1 <= segments_2) ”
  &&  “ (segments_2 <= (i_2 + 1 )) ”
  &&  “ (old_2 = (Zlength (base_products_2))) ”
  &&  “ (base_products_2 = (sublist (0) (old_2) (products_before_append))) ”
  &&  “ (1 <= old_2) ”
  &&  “ (old_2 <= count_2) ”
  &&  “ (count_2 <= x_pre) ”
  &&  “ (0 <= j_2) ”
  &&  “ (j_2 <= old_2) ”
  &&  “ (count_2 = (Zlength (products_before_append))) ”
  &&  “ (reaches_2 = 0) ”
  &&  “ ((Zlength (bitmap_2)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count_2)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i_2 segments_2 base_products_2 ) ”
  &&  “ (ValuableForcedHistory x_pre values i_2 segments_2 base_products_2 ) ”
  &&  “ (ValuableAlignedHistory x_pre values i_2 segments_2 base_products_2 ) ”
  &&  “ (ValuableClosureState x_pre segment_2 v_2 base_products_2 j_2 products_before_append reaches_2 ) ”
  &&  “ (ValuableBitmap x_pre products_before_append bitmap_2 ) ”
  &&  ((( &( "p" ) )) # Int  |-> ((Znth (j_2 - 0 ) products_before_append 0) * v_2 ))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  (IntArray.seg products_buf_2 0 count_2 products_before_append )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "v" ) )) # Int  |-> v_2)
  **  ((( &( "segments" ) )) # Int  |-> segments_2)
  **  ((( &( "old" ) )) # Int  |-> old_2)
  **  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "j" ) )) # Int  |-> j_2)
  **  ((( &( "reaches" ) )) # Int  |-> reaches_2)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf_2)
  **  (IntArray.undef_seg products_buf_2 count_2 (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used_2)
  **  (UCharArray.full used_2 (x_pre + 1 ) bitmap_2 ))
.

Definition solver_entail_wit_3_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used_2: Z) (products_buf_2: Z) (segment_2: (@list Z)) (bitmap_2: (@list Z)) (reaches_2: Z) (j_2: Z) (count_2: Z) (base_products_2: (@list Z)) (old_2: Z) (segments_2: Z) (v_2: Z) (i_2: Z) (products_before_append: (@list Z)) (PreH1 : ((x_pre % ( ((Znth (j_2 - 0 ) products_before_append 0) * v_2 ) ) ) = 0)) (PreH2 : ((Znth (j_2 - 0 ) products_before_append 0) <= (x_pre ÷ v_2 ))) (PreH3 : (j_2 < old_2)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 100000)) (PreH7 : (1 <= (Zlength (values)))) (PreH8 : ((Zlength (values)) <= 100000)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH10 : (Pre x_pre values )) (PreH11 : (0 <= i_2)) (PreH12 : (i_2 < n_pre)) (PreH13 : (v_2 = (Znth i_2 values 0))) (PreH14 : (1 <= v_2)) (PreH15 : (v_2 <= x_pre)) (PreH16 : ((x_pre % ( v_2 ) ) = 0)) (PreH17 : (1 <= segments_2)) (PreH18 : (segments_2 <= (i_2 + 1 ))) (PreH19 : (old_2 = (Zlength (base_products_2)))) (PreH20 : (base_products_2 = (sublist (0) (old_2) (products_before_append)))) (PreH21 : (1 <= old_2)) (PreH22 : (old_2 <= count_2)) (PreH23 : (count_2 <= x_pre)) (PreH24 : (0 <= j_2)) (PreH25 : (j_2 <= old_2)) (PreH26 : (count_2 = (Zlength (products_before_append)))) (PreH27 : (reaches_2 = 0)) (PreH28 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH29 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count_2)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH30 : (ValuableOuterState x_pre values i_2 segments_2 base_products_2 )) (PreH31 : (ValuableForcedHistory x_pre values i_2 segments_2 base_products_2 )) (PreH32 : (ValuableAlignedHistory x_pre values i_2 segments_2 base_products_2 )) (PreH33 : (ValuableClosureState x_pre segment_2 v_2 base_products_2 j_2 products_before_append reaches_2 )) (PreH34 : (ValuableBitmap x_pre products_before_append bitmap_2 )),
  (IntArray.seg products_buf_2 0 count_2 products_before_append )
  **  ((( &( "p" ) )) # Int  |-> ((Znth (j_2 - 0 ) products_before_append 0) * v_2 ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "v" ) )) # Int  |-> v_2)
  **  ((( &( "segments" ) )) # Int  |-> segments_2)
  **  ((( &( "old" ) )) # Int  |-> old_2)
  **  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "j" ) )) # Int  |-> j_2)
  **  ((( &( "reaches" ) )) # Int  |-> reaches_2)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf_2)
  **  (IntArray.undef_seg products_buf_2 count_2 (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used_2)
  **  (UCharArray.full used_2 (x_pre + 1 ) bitmap_2 )
|--
  (EX (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z),
  “ (1 <= ((Znth (j - 0 ) products_before_append 0) * v )) ”
  &&  “ (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre) ”
  &&  “ (reaches <= INT_MAX) ”
  &&  “ (j <= INT_MAX) ”
  &&  “ (count <= INT_MAX) ”
  &&  “ (old <= INT_MAX) ”
  &&  “ (segments <= INT_MAX) ”
  &&  “ (v <= INT_MAX) ”
  &&  “ (i <= INT_MAX) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (reaches >= INT_MIN) ”
  &&  “ (j >= INT_MIN) ”
  &&  “ (count >= INT_MIN) ”
  &&  “ (old >= INT_MIN) ”
  &&  “ (segments >= INT_MIN) ”
  &&  “ (v >= INT_MIN) ”
  &&  “ (i >= INT_MIN) ”
  &&  “ (n_pre >= INT_MIN) ”
  &&  “ ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0) ”
  &&  “ ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v )) ”
  &&  “ (j < old) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products_before_append))) ”
  &&  “ (1 <= old) ”
  &&  “ (old <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= old) ”
  &&  “ (count = (Zlength (products_before_append))) ”
  &&  “ (reaches = 1) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products j products_before_append reaches ) ”
  &&  “ (ValuableBitmap x_pre products_before_append bitmap ) ”
  &&  ((( &( "p" ) )) # Int  |-> ((Znth (j - 0 ) products_before_append 0) * v ))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  (IntArray.seg products_buf 0 count products_before_append )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap ))
  ||
  (“ (1 <= ((Znth (j_2 - 0 ) products_before_append 0) * v_2 )) ”
  &&  “ (((Znth (j_2 - 0 ) products_before_append 0) * v_2 ) <= x_pre) ”
  &&  “ (reaches_2 <= INT_MAX) ”
  &&  “ (j_2 <= INT_MAX) ”
  &&  “ (count_2 <= INT_MAX) ”
  &&  “ (old_2 <= INT_MAX) ”
  &&  “ (segments_2 <= INT_MAX) ”
  &&  “ (v_2 <= INT_MAX) ”
  &&  “ (i_2 <= INT_MAX) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (reaches_2 >= INT_MIN) ”
  &&  “ (j_2 >= INT_MIN) ”
  &&  “ (count_2 >= INT_MIN) ”
  &&  “ (old_2 >= INT_MIN) ”
  &&  “ (segments_2 >= INT_MIN) ”
  &&  “ (v_2 >= INT_MIN) ”
  &&  “ (i_2 >= INT_MIN) ”
  &&  “ (n_pre >= INT_MIN) ”
  &&  “ ((x_pre % ( ((Znth (j_2 - 0 ) products_before_append 0) * v_2 ) ) ) = 0) ”
  &&  “ ((Znth (j_2 - 0 ) products_before_append 0) <= (x_pre ÷ v_2 )) ”
  &&  “ (j_2 < old_2) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i_2) ”
  &&  “ (i_2 < n_pre) ”
  &&  “ (v_2 = (Znth i_2 values 0)) ”
  &&  “ (1 <= v_2) ”
  &&  “ (v_2 <= x_pre) ”
  &&  “ ((x_pre % ( v_2 ) ) = 0) ”
  &&  “ (1 <= segments_2) ”
  &&  “ (segments_2 <= (i_2 + 1 )) ”
  &&  “ (old_2 = (Zlength (base_products_2))) ”
  &&  “ (base_products_2 = (sublist (0) (old_2) (products_before_append))) ”
  &&  “ (1 <= old_2) ”
  &&  “ (old_2 <= count_2) ”
  &&  “ (count_2 <= x_pre) ”
  &&  “ (0 <= j_2) ”
  &&  “ (j_2 <= old_2) ”
  &&  “ (count_2 = (Zlength (products_before_append))) ”
  &&  “ (reaches_2 = 0) ”
  &&  “ ((Zlength (bitmap_2)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count_2)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i_2 segments_2 base_products_2 ) ”
  &&  “ (ValuableForcedHistory x_pre values i_2 segments_2 base_products_2 ) ”
  &&  “ (ValuableAlignedHistory x_pre values i_2 segments_2 base_products_2 ) ”
  &&  “ (ValuableClosureState x_pre segment_2 v_2 base_products_2 j_2 products_before_append reaches_2 ) ”
  &&  “ (ValuableBitmap x_pre products_before_append bitmap_2 ) ”
  &&  ((( &( "p" ) )) # Int  |-> ((Znth (j_2 - 0 ) products_before_append 0) * v_2 ))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  (IntArray.seg products_buf_2 0 count_2 products_before_append )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "v" ) )) # Int  |-> v_2)
  **  ((( &( "segments" ) )) # Int  |-> segments_2)
  **  ((( &( "old" ) )) # Int  |-> old_2)
  **  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "j" ) )) # Int  |-> j_2)
  **  ((( &( "reaches" ) )) # Int  |-> reaches_2)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf_2)
  **  (IntArray.undef_seg products_buf_2 count_2 (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used_2)
  **  (UCharArray.full used_2 (x_pre + 1 ) bitmap_2 ))
.

Definition solver_entail_wit_4_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap 0) = 0)) (PreH2 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH3 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (j <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (old <= INT_MAX)) (PreH8 : (segments <= INT_MAX)) (PreH9 : (v <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (reaches >= INT_MIN)) (PreH13 : (j >= INT_MIN)) (PreH14 : (count >= INT_MIN)) (PreH15 : (old >= INT_MIN)) (PreH16 : (segments >= INT_MIN)) (PreH17 : (v >= INT_MIN)) (PreH18 : (i >= INT_MIN)) (PreH19 : (n_pre >= INT_MIN)) (PreH20 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH21 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH22 : (j < old)) (PreH23 : (n_pre = (Zlength (values)))) (PreH24 : (2 <= x_pre)) (PreH25 : (x_pre <= 100000)) (PreH26 : (1 <= (Zlength (values)))) (PreH27 : ((Zlength (values)) <= 100000)) (PreH28 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH29 : (Pre x_pre values )) (PreH30 : (0 <= i)) (PreH31 : (i < n_pre)) (PreH32 : (v = (Znth i values 0))) (PreH33 : (1 <= v)) (PreH34 : (v <= x_pre)) (PreH35 : ((x_pre % ( v ) ) = 0)) (PreH36 : (1 <= segments)) (PreH37 : (segments <= (i + 1 ))) (PreH38 : (old = (Zlength (base_products)))) (PreH39 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH40 : (1 <= old)) (PreH41 : (old <= count)) (PreH42 : (count <= x_pre)) (PreH43 : (0 <= j)) (PreH44 : (j <= old)) (PreH45 : (count = (Zlength (products_before_append)))) (PreH46 : (reaches = 1)) (PreH47 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH48 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH49 : (ValuableOuterState x_pre values i segments base_products )) (PreH50 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH51 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH52 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH53 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.seg products_buf 0 (count + 1 ) (app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * v )) ((@nil Z))))) )
  **  (IntArray.undef_seg products_buf (count + 1 ) (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) (replace_Znth (((Znth (j - 0 ) products_before_append 0) * v )) (1) (bitmap)) )
  **  ((( &( "p" ) )) # Int  |-> ((Znth (j - 0 ) products_before_append 0) * v ))
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap 0) = 0) ”
  &&  “ (1 <= ((Znth (j - 0 ) products_before_append 0) * v )) ”
  &&  “ (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre) ”
  &&  “ (reaches <= INT_MAX) ”
  &&  “ (j <= INT_MAX) ”
  &&  “ (count <= INT_MAX) ”
  &&  “ (old <= INT_MAX) ”
  &&  “ (segments <= INT_MAX) ”
  &&  “ (v <= INT_MAX) ”
  &&  “ (i <= INT_MAX) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (reaches >= INT_MIN) ”
  &&  “ (j >= INT_MIN) ”
  &&  “ (count >= INT_MIN) ”
  &&  “ (old >= INT_MIN) ”
  &&  “ (segments >= INT_MIN) ”
  &&  “ (v >= INT_MIN) ”
  &&  “ (i >= INT_MIN) ”
  &&  “ (n_pre >= INT_MIN) ”
  &&  “ ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0) ”
  &&  “ ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v )) ”
  &&  “ (j < old) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products_before_append))) ”
  &&  “ (1 <= old) ”
  &&  “ (old <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= old) ”
  &&  “ (count = (Zlength (products_before_append))) ”
  &&  “ (reaches = 1) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products j products_before_append reaches ) ”
  &&  “ (ValuableBitmap x_pre products_before_append bitmap ) ”
  &&  ((( &( "p" ) )) # Int  |-> ((Znth (j - 0 ) products_before_append 0) * v ))
  **  (IntArray.seg products_buf 0 (count + 1 ) (app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * v )) ((@nil Z))))) )
  **  (IntArray.undef_seg products_buf (count + 1 ) (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) (replace_Znth (((Znth (j - 0 ) products_before_append 0) * v )) (1) (bitmap)) )
  **  (IntArray.full a_pre n_pre values )
.

Definition solver_entail_wit_4_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment_2: (@list Z)) (bitmap_2: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products_2: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap_2 0) = 0)) (PreH2 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH3 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (j <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (old <= INT_MAX)) (PreH8 : (segments <= INT_MAX)) (PreH9 : (v <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (reaches >= INT_MIN)) (PreH13 : (j >= INT_MIN)) (PreH14 : (count >= INT_MIN)) (PreH15 : (old >= INT_MIN)) (PreH16 : (segments >= INT_MIN)) (PreH17 : (v >= INT_MIN)) (PreH18 : (i >= INT_MIN)) (PreH19 : (n_pre >= INT_MIN)) (PreH20 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH21 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH22 : (j < old)) (PreH23 : (n_pre = (Zlength (values)))) (PreH24 : (2 <= x_pre)) (PreH25 : (x_pre <= 100000)) (PreH26 : (1 <= (Zlength (values)))) (PreH27 : ((Zlength (values)) <= 100000)) (PreH28 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH29 : (Pre x_pre values )) (PreH30 : (0 <= i)) (PreH31 : (i < n_pre)) (PreH32 : (v = (Znth i values 0))) (PreH33 : (1 <= v)) (PreH34 : (v <= x_pre)) (PreH35 : ((x_pre % ( v ) ) = 0)) (PreH36 : (1 <= segments)) (PreH37 : (segments <= (i + 1 ))) (PreH38 : (old = (Zlength (base_products_2)))) (PreH39 : (base_products_2 = (sublist (0) (old) (products_before_append)))) (PreH40 : (1 <= old)) (PreH41 : (old <= count)) (PreH42 : (count <= x_pre)) (PreH43 : (0 <= j)) (PreH44 : (j <= old)) (PreH45 : (count = (Zlength (products_before_append)))) (PreH46 : (reaches = 0)) (PreH47 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH48 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH49 : (ValuableOuterState x_pre values i segments base_products_2 )) (PreH50 : (ValuableForcedHistory x_pre values i segments base_products_2 )) (PreH51 : (ValuableAlignedHistory x_pre values i segments base_products_2 )) (PreH52 : (ValuableClosureState x_pre segment_2 v base_products_2 j products_before_append reaches )) (PreH53 : (ValuableBitmap x_pre products_before_append bitmap_2 )),
  (IntArray.seg products_buf 0 (count + 1 ) (app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * v )) ((@nil Z))))) )
  **  (IntArray.undef_seg products_buf (count + 1 ) (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) (replace_Znth (((Znth (j - 0 ) products_before_append 0) * v )) (1) (bitmap_2)) )
  **  ((( &( "p" ) )) # Int  |-> ((Znth (j - 0 ) products_before_append 0) * v ))
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap_2 0) = 0) ”
  &&  “ (1 <= ((Znth (j - 0 ) products_before_append 0) * v )) ”
  &&  “ (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre) ”
  &&  “ (reaches <= INT_MAX) ”
  &&  “ (j <= INT_MAX) ”
  &&  “ (count <= INT_MAX) ”
  &&  “ (old <= INT_MAX) ”
  &&  “ (segments <= INT_MAX) ”
  &&  “ (v <= INT_MAX) ”
  &&  “ (i <= INT_MAX) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (reaches >= INT_MIN) ”
  &&  “ (j >= INT_MIN) ”
  &&  “ (count >= INT_MIN) ”
  &&  “ (old >= INT_MIN) ”
  &&  “ (segments >= INT_MIN) ”
  &&  “ (v >= INT_MIN) ”
  &&  “ (i >= INT_MIN) ”
  &&  “ (n_pre >= INT_MIN) ”
  &&  “ ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0) ”
  &&  “ ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v )) ”
  &&  “ (j < old) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (old = (Zlength (base_products_2))) ”
  &&  “ (base_products_2 = (sublist (0) (old) (products_before_append))) ”
  &&  “ (1 <= old) ”
  &&  “ (old <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= old) ”
  &&  “ (count = (Zlength (products_before_append))) ”
  &&  “ (reaches = 0) ”
  &&  “ ((Zlength (bitmap_2)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments base_products_2 ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments base_products_2 ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments base_products_2 ) ”
  &&  “ (ValuableClosureState x_pre segment_2 v base_products_2 j products_before_append reaches ) ”
  &&  “ (ValuableBitmap x_pre products_before_append bitmap_2 ) ”
  &&  ((( &( "p" ) )) # Int  |-> ((Znth (j - 0 ) products_before_append 0) * v ))
  **  (IntArray.seg products_buf 0 (count + 1 ) (app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * v )) ((@nil Z))))) )
  **  (IntArray.undef_seg products_buf (count + 1 ) (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) (replace_Znth (((Znth (j - 0 ) products_before_append 0) * v )) (1) (bitmap_2)) )
  **  (IntArray.full a_pre n_pre values )
.

Definition solver_entail_wit_5_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment_2: (@list Z)) (bitmap_2: (@list Z)) (reaches: Z) (j: Z) (count: Z) (products_2: (@list Z)) (base_products_2: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (PreH1 : (j >= old)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (v = (Znth i values 0))) (PreH12 : (1 <= v)) (PreH13 : (v <= x_pre)) (PreH14 : ((x_pre % ( v ) ) = 0)) (PreH15 : (1 <= segments)) (PreH16 : (segments <= (i + 1 ))) (PreH17 : (old = (Zlength (base_products_2)))) (PreH18 : (base_products_2 = (sublist (0) (old) (products_2)))) (PreH19 : (1 <= old)) (PreH20 : (old <= count)) (PreH21 : (count <= x_pre)) (PreH22 : (0 <= j)) (PreH23 : (j <= old)) (PreH24 : (count = (Zlength (products_2)))) (PreH25 : (reaches = 1)) (PreH26 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH27 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < count)) -> ((1 <= (Znth k_4 products_2 0)) /\ ((Znth k_4 products_2 0) <= x_pre)))) (PreH28 : (ValuableOuterState x_pre values i segments base_products_2 )) (PreH29 : (ValuableForcedHistory x_pre values i segments base_products_2 )) (PreH30 : (ValuableAlignedHistory x_pre values i segments base_products_2 )) (PreH31 : (ValuableClosureState x_pre segment_2 v base_products_2 j products_2 reaches )) (PreH32 : (ValuableBitmap x_pre products_2 bitmap_2 )),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products_2 )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap_2 )
|--
  EX (segment: (@list Z)) (bitmap: (@list Z)) (products: (@list Z)) (base_products: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products))) ”
  &&  “ (1 <= old) ”
  &&  “ (old <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (count = (Zlength (products))) ”
  &&  “ (reaches = 1) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products old products reaches ) ”
  &&  “ (ValuableBitmap x_pre products bitmap ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment_2: (@list Z)) (bitmap_2: (@list Z)) (reaches: Z) (j: Z) (count: Z) (products_2: (@list Z)) (base_products_2: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (PreH1 : (j >= old)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (v = (Znth i values 0))) (PreH12 : (1 <= v)) (PreH13 : (v <= x_pre)) (PreH14 : ((x_pre % ( v ) ) = 0)) (PreH15 : (1 <= segments)) (PreH16 : (segments <= (i + 1 ))) (PreH17 : (old = (Zlength (base_products_2)))) (PreH18 : (base_products_2 = (sublist (0) (old) (products_2)))) (PreH19 : (1 <= old)) (PreH20 : (old <= count)) (PreH21 : (count <= x_pre)) (PreH22 : (0 <= j)) (PreH23 : (j <= old)) (PreH24 : (count = (Zlength (products_2)))) (PreH25 : (reaches = 1)) (PreH26 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH27 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < count)) -> ((1 <= (Znth k_4 products_2 0)) /\ ((Znth k_4 products_2 0) <= x_pre)))) (PreH28 : (ValuableOuterState x_pre values i segments base_products_2 )) (PreH29 : (ValuableForcedHistory x_pre values i segments base_products_2 )) (PreH30 : (ValuableAlignedHistory x_pre values i segments base_products_2 )) (PreH31 : (ValuableClosureState x_pre segment_2 v base_products_2 j products_2 reaches )) (PreH32 : (ValuableBitmap x_pre products_2 bitmap_2 )),
  TT && emp 
|--
  EX (segment: (@list Z)),
  “ ((Zlength ((sublist (0) (old) (products_2)))) = (Zlength ((sublist (0) ((Zlength ((sublist (0) (old) (products_2))))) (products_2))))) ”
  &&  “ (ValuableOuterState x_pre values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_2))))) (products_2)) ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_2))))) (products_2)) ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_2))))) (products_2)) ) ”
  &&  “ (ValuableClosureState x_pre segment (Znth i values 0) (sublist (0) ((Zlength ((sublist (0) (old) (products_2))))) (products_2)) (Zlength ((sublist (0) (old) (products_2)))) products_2 1 ) ”
  &&  emp
).

Definition solver_entail_wit_5_2 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment_2: (@list Z)) (bitmap_2: (@list Z)) (reaches: Z) (j: Z) (count: Z) (products_2: (@list Z)) (base_products_2: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (PreH1 : (j >= old)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (v = (Znth i values 0))) (PreH12 : (1 <= v)) (PreH13 : (v <= x_pre)) (PreH14 : ((x_pre % ( v ) ) = 0)) (PreH15 : (1 <= segments)) (PreH16 : (segments <= (i + 1 ))) (PreH17 : (old = (Zlength (base_products_2)))) (PreH18 : (base_products_2 = (sublist (0) (old) (products_2)))) (PreH19 : (1 <= old)) (PreH20 : (old <= count)) (PreH21 : (count <= x_pre)) (PreH22 : (0 <= j)) (PreH23 : (j <= old)) (PreH24 : (count = (Zlength (products_2)))) (PreH25 : (reaches = 0)) (PreH26 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH27 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < count)) -> ((1 <= (Znth k_4 products_2 0)) /\ ((Znth k_4 products_2 0) <= x_pre)))) (PreH28 : (ValuableOuterState x_pre values i segments base_products_2 )) (PreH29 : (ValuableForcedHistory x_pre values i segments base_products_2 )) (PreH30 : (ValuableAlignedHistory x_pre values i segments base_products_2 )) (PreH31 : (ValuableClosureState x_pre segment_2 v base_products_2 j products_2 reaches )) (PreH32 : (ValuableBitmap x_pre products_2 bitmap_2 )),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products_2 )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap_2 )
|--
  EX (segment: (@list Z)) (bitmap: (@list Z)) (products: (@list Z)) (base_products: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products))) ”
  &&  “ (1 <= old) ”
  &&  “ (old <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (count = (Zlength (products))) ”
  &&  “ (reaches = 0) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products old products reaches ) ”
  &&  “ (ValuableBitmap x_pre products bitmap ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment_2: (@list Z)) (bitmap_2: (@list Z)) (reaches: Z) (j: Z) (count: Z) (products_2: (@list Z)) (base_products_2: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (PreH1 : (j >= old)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (v = (Znth i values 0))) (PreH12 : (1 <= v)) (PreH13 : (v <= x_pre)) (PreH14 : ((x_pre % ( v ) ) = 0)) (PreH15 : (1 <= segments)) (PreH16 : (segments <= (i + 1 ))) (PreH17 : (old = (Zlength (base_products_2)))) (PreH18 : (base_products_2 = (sublist (0) (old) (products_2)))) (PreH19 : (1 <= old)) (PreH20 : (old <= count)) (PreH21 : (count <= x_pre)) (PreH22 : (0 <= j)) (PreH23 : (j <= old)) (PreH24 : (count = (Zlength (products_2)))) (PreH25 : (reaches = 0)) (PreH26 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH27 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < count)) -> ((1 <= (Znth k_4 products_2 0)) /\ ((Znth k_4 products_2 0) <= x_pre)))) (PreH28 : (ValuableOuterState x_pre values i segments base_products_2 )) (PreH29 : (ValuableForcedHistory x_pre values i segments base_products_2 )) (PreH30 : (ValuableAlignedHistory x_pre values i segments base_products_2 )) (PreH31 : (ValuableClosureState x_pre segment_2 v base_products_2 j products_2 reaches )) (PreH32 : (ValuableBitmap x_pre products_2 bitmap_2 )),
  TT && emp 
|--
  EX (segment: (@list Z)),
  “ ((Zlength ((sublist (0) (old) (products_2)))) = (Zlength ((sublist (0) ((Zlength ((sublist (0) (old) (products_2))))) (products_2))))) ”
  &&  “ (ValuableOuterState x_pre values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_2))))) (products_2)) ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_2))))) (products_2)) ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_2))))) (products_2)) ) ”
  &&  “ (ValuableClosureState x_pre segment (Znth i values 0) (sublist (0) ((Zlength ((sublist (0) (old) (products_2))))) (products_2)) (Zlength ((sublist (0) (old) (products_2)))) products_2 0 ) ”
  &&  emp
).

Definition solver_entail_wit_6_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment_2: (@list Z)) (bitmap_2: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products_2: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : (((Znth (j - 0 ) products_before_append 0) * v ) = x_pre)) (PreH2 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap_2 0) = 0)) (PreH3 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH4 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH5 : (reaches <= INT_MAX)) (PreH6 : (j <= INT_MAX)) (PreH7 : (count <= INT_MAX)) (PreH8 : (old <= INT_MAX)) (PreH9 : (segments <= INT_MAX)) (PreH10 : (v <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (reaches >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (count >= INT_MIN)) (PreH16 : (old >= INT_MIN)) (PreH17 : (segments >= INT_MIN)) (PreH18 : (v >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH22 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH23 : (j < old)) (PreH24 : (n_pre = (Zlength (values)))) (PreH25 : (2 <= x_pre)) (PreH26 : (x_pre <= 100000)) (PreH27 : (1 <= (Zlength (values)))) (PreH28 : ((Zlength (values)) <= 100000)) (PreH29 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH30 : (Pre x_pre values )) (PreH31 : (0 <= i)) (PreH32 : (i < n_pre)) (PreH33 : (v = (Znth i values 0))) (PreH34 : (1 <= v)) (PreH35 : (v <= x_pre)) (PreH36 : ((x_pre % ( v ) ) = 0)) (PreH37 : (1 <= segments)) (PreH38 : (segments <= (i + 1 ))) (PreH39 : (old = (Zlength (base_products_2)))) (PreH40 : (base_products_2 = (sublist (0) (old) (products_before_append)))) (PreH41 : (1 <= old)) (PreH42 : (old <= count)) (PreH43 : (count <= x_pre)) (PreH44 : (0 <= j)) (PreH45 : (j <= old)) (PreH46 : (count = (Zlength (products_before_append)))) (PreH47 : (reaches = 1)) (PreH48 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH49 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH50 : (ValuableOuterState x_pre values i segments base_products_2 )) (PreH51 : (ValuableForcedHistory x_pre values i segments base_products_2 )) (PreH52 : (ValuableAlignedHistory x_pre values i segments base_products_2 )) (PreH53 : (ValuableClosureState x_pre segment_2 v base_products_2 j products_before_append reaches )) (PreH54 : (ValuableBitmap x_pre products_before_append bitmap_2 )),
  (IntArray.seg products_buf 0 (count + 1 ) (app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * v )) ((@nil Z))))) )
  **  (IntArray.undef_seg products_buf (count + 1 ) (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) (replace_Znth (((Znth (j - 0 ) products_before_append 0) * v )) (1) (bitmap_2)) )
  **  (IntArray.full a_pre n_pre values )
|--
  EX (segment: (@list Z)) (bitmap: (@list Z)) (products: (@list Z)) (base_products: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products))) ”
  &&  “ (1 <= old) ”
  &&  “ (old <= (count + 1 )) ”
  &&  “ ((count + 1 ) <= x_pre) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= old) ”
  &&  “ ((count + 1 ) = (Zlength (products))) ”
  &&  “ (1 = 1) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (count + 1 ))) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products (j + 1 ) products 1 ) ”
  &&  “ (ValuableBitmap x_pre products bitmap ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 (count + 1 ) products )
  **  (IntArray.undef_seg products_buf (count + 1 ) (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment_2: (@list Z)) (bitmap_2: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products_2: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : (((Znth (j - 0 ) products_before_append 0) * v ) = x_pre)) (PreH2 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap_2 0) = 0)) (PreH3 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH4 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH5 : (reaches <= INT_MAX)) (PreH6 : (j <= INT_MAX)) (PreH7 : (count <= INT_MAX)) (PreH8 : (old <= INT_MAX)) (PreH9 : (segments <= INT_MAX)) (PreH10 : (v <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (reaches >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (count >= INT_MIN)) (PreH16 : (old >= INT_MIN)) (PreH17 : (segments >= INT_MIN)) (PreH18 : (v >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH22 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH23 : (j < old)) (PreH24 : (n_pre = (Zlength (values)))) (PreH25 : (2 <= x_pre)) (PreH26 : (x_pre <= 100000)) (PreH27 : (1 <= (Zlength (values)))) (PreH28 : ((Zlength (values)) <= 100000)) (PreH29 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH30 : (Pre x_pre values )) (PreH31 : (0 <= i)) (PreH32 : (i < n_pre)) (PreH33 : (v = (Znth i values 0))) (PreH34 : (1 <= v)) (PreH35 : (v <= x_pre)) (PreH36 : ((x_pre % ( v ) ) = 0)) (PreH37 : (1 <= segments)) (PreH38 : (segments <= (i + 1 ))) (PreH39 : (old = (Zlength (base_products_2)))) (PreH40 : (base_products_2 = (sublist (0) (old) (products_before_append)))) (PreH41 : (1 <= old)) (PreH42 : (old <= count)) (PreH43 : (count <= x_pre)) (PreH44 : (0 <= j)) (PreH45 : (j <= old)) (PreH46 : (count = (Zlength (products_before_append)))) (PreH47 : (reaches = 1)) (PreH48 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH49 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH50 : (ValuableOuterState x_pre values i segments base_products_2 )) (PreH51 : (ValuableForcedHistory x_pre values i segments base_products_2 )) (PreH52 : (ValuableAlignedHistory x_pre values i segments base_products_2 )) (PreH53 : (ValuableClosureState x_pre segment_2 v base_products_2 j products_before_append reaches )) (PreH54 : (ValuableBitmap x_pre products_before_append bitmap_2 )),
  TT && emp 
|--
  EX (segment: (@list Z)),
  “ ((Zlength ((sublist (0) (old) (products_before_append)))) = (Zlength ((sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) ((app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z)))))))))) ”
  &&  “ ((Zlength ((sublist (0) (old) (products_before_append)))) <= ((Zlength (products_before_append)) + 1 )) ”
  &&  “ (((Zlength (products_before_append)) + 1 ) <= ((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (Zlength ((sublist (0) (old) (products_before_append))))) ”
  &&  “ (((Zlength (products_before_append)) + 1 ) = (Zlength ((app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z)))))))) ”
  &&  “ ((Zlength ((replace_Znth (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) (1) (bitmap_2)))) = (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) ) + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < ((Zlength (products_before_append)) + 1 ))) -> ((1 <= (Znth k_2 (app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z))))) 0)) /\ ((Znth k_2 (app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z))))) 0) <= ((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )))) ”
  &&  “ (ValuableOuterState ((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) ) values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) ((app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z))))))) ) ”
  &&  “ (ValuableForcedHistory ((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) ) values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) ((app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z))))))) ) ”
  &&  “ (ValuableAlignedHistory ((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) ) values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) ((app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z))))))) ) ”
  &&  “ (ValuableClosureState ((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) ) segment (Znth i values 0) (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) ((app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z))))))) (j + 1 ) (app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z))))) 1 ) ”
  &&  “ (ValuableBitmap ((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) ) (app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z))))) (replace_Znth (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) (1) (bitmap_2)) ) ”
  &&  emp
).

Definition solver_entail_wit_6_2 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment_2: (@list Z)) (bitmap_2: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products_2: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : (((Znth (j - 0 ) products_before_append 0) * v ) = x_pre)) (PreH2 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap_2 0) = 0)) (PreH3 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH4 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH5 : (reaches <= INT_MAX)) (PreH6 : (j <= INT_MAX)) (PreH7 : (count <= INT_MAX)) (PreH8 : (old <= INT_MAX)) (PreH9 : (segments <= INT_MAX)) (PreH10 : (v <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (reaches >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (count >= INT_MIN)) (PreH16 : (old >= INT_MIN)) (PreH17 : (segments >= INT_MIN)) (PreH18 : (v >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH22 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH23 : (j < old)) (PreH24 : (n_pre = (Zlength (values)))) (PreH25 : (2 <= x_pre)) (PreH26 : (x_pre <= 100000)) (PreH27 : (1 <= (Zlength (values)))) (PreH28 : ((Zlength (values)) <= 100000)) (PreH29 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH30 : (Pre x_pre values )) (PreH31 : (0 <= i)) (PreH32 : (i < n_pre)) (PreH33 : (v = (Znth i values 0))) (PreH34 : (1 <= v)) (PreH35 : (v <= x_pre)) (PreH36 : ((x_pre % ( v ) ) = 0)) (PreH37 : (1 <= segments)) (PreH38 : (segments <= (i + 1 ))) (PreH39 : (old = (Zlength (base_products_2)))) (PreH40 : (base_products_2 = (sublist (0) (old) (products_before_append)))) (PreH41 : (1 <= old)) (PreH42 : (old <= count)) (PreH43 : (count <= x_pre)) (PreH44 : (0 <= j)) (PreH45 : (j <= old)) (PreH46 : (count = (Zlength (products_before_append)))) (PreH47 : (reaches = 0)) (PreH48 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH49 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH50 : (ValuableOuterState x_pre values i segments base_products_2 )) (PreH51 : (ValuableForcedHistory x_pre values i segments base_products_2 )) (PreH52 : (ValuableAlignedHistory x_pre values i segments base_products_2 )) (PreH53 : (ValuableClosureState x_pre segment_2 v base_products_2 j products_before_append reaches )) (PreH54 : (ValuableBitmap x_pre products_before_append bitmap_2 )),
  (IntArray.seg products_buf 0 (count + 1 ) (app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * v )) ((@nil Z))))) )
  **  (IntArray.undef_seg products_buf (count + 1 ) (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) (replace_Znth (((Znth (j - 0 ) products_before_append 0) * v )) (1) (bitmap_2)) )
  **  (IntArray.full a_pre n_pre values )
|--
  EX (segment: (@list Z)) (bitmap: (@list Z)) (products: (@list Z)) (base_products: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products))) ”
  &&  “ (1 <= old) ”
  &&  “ (old <= (count + 1 )) ”
  &&  “ ((count + 1 ) <= x_pre) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= old) ”
  &&  “ ((count + 1 ) = (Zlength (products))) ”
  &&  “ (1 = 1) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (count + 1 ))) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products (j + 1 ) products 1 ) ”
  &&  “ (ValuableBitmap x_pre products bitmap ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 (count + 1 ) products )
  **  (IntArray.undef_seg products_buf (count + 1 ) (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment_2: (@list Z)) (bitmap_2: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products_2: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : (((Znth (j - 0 ) products_before_append 0) * v ) = x_pre)) (PreH2 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap_2 0) = 0)) (PreH3 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH4 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH5 : (reaches <= INT_MAX)) (PreH6 : (j <= INT_MAX)) (PreH7 : (count <= INT_MAX)) (PreH8 : (old <= INT_MAX)) (PreH9 : (segments <= INT_MAX)) (PreH10 : (v <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (reaches >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (count >= INT_MIN)) (PreH16 : (old >= INT_MIN)) (PreH17 : (segments >= INT_MIN)) (PreH18 : (v >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH22 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH23 : (j < old)) (PreH24 : (n_pre = (Zlength (values)))) (PreH25 : (2 <= x_pre)) (PreH26 : (x_pre <= 100000)) (PreH27 : (1 <= (Zlength (values)))) (PreH28 : ((Zlength (values)) <= 100000)) (PreH29 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH30 : (Pre x_pre values )) (PreH31 : (0 <= i)) (PreH32 : (i < n_pre)) (PreH33 : (v = (Znth i values 0))) (PreH34 : (1 <= v)) (PreH35 : (v <= x_pre)) (PreH36 : ((x_pre % ( v ) ) = 0)) (PreH37 : (1 <= segments)) (PreH38 : (segments <= (i + 1 ))) (PreH39 : (old = (Zlength (base_products_2)))) (PreH40 : (base_products_2 = (sublist (0) (old) (products_before_append)))) (PreH41 : (1 <= old)) (PreH42 : (old <= count)) (PreH43 : (count <= x_pre)) (PreH44 : (0 <= j)) (PreH45 : (j <= old)) (PreH46 : (count = (Zlength (products_before_append)))) (PreH47 : (reaches = 0)) (PreH48 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH49 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH50 : (ValuableOuterState x_pre values i segments base_products_2 )) (PreH51 : (ValuableForcedHistory x_pre values i segments base_products_2 )) (PreH52 : (ValuableAlignedHistory x_pre values i segments base_products_2 )) (PreH53 : (ValuableClosureState x_pre segment_2 v base_products_2 j products_before_append reaches )) (PreH54 : (ValuableBitmap x_pre products_before_append bitmap_2 )),
  TT && emp 
|--
  EX (segment: (@list Z)),
  “ ((Zlength ((sublist (0) (old) (products_before_append)))) = (Zlength ((sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) ((app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z)))))))))) ”
  &&  “ ((Zlength ((sublist (0) (old) (products_before_append)))) <= ((Zlength (products_before_append)) + 1 )) ”
  &&  “ (((Zlength (products_before_append)) + 1 ) <= ((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (Zlength ((sublist (0) (old) (products_before_append))))) ”
  &&  “ (((Zlength (products_before_append)) + 1 ) = (Zlength ((app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z)))))))) ”
  &&  “ ((Zlength ((replace_Znth (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) (1) (bitmap_2)))) = (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) ) + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < ((Zlength (products_before_append)) + 1 ))) -> ((1 <= (Znth k_2 (app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z))))) 0)) /\ ((Znth k_2 (app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z))))) 0) <= ((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )))) ”
  &&  “ (ValuableOuterState ((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) ) values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) ((app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z))))))) ) ”
  &&  “ (ValuableForcedHistory ((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) ) values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) ((app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z))))))) ) ”
  &&  “ (ValuableAlignedHistory ((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) ) values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) ((app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z))))))) ) ”
  &&  “ (ValuableClosureState ((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) ) segment (Znth i values 0) (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) ((app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z))))))) (j + 1 ) (app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z))))) 1 ) ”
  &&  “ (ValuableBitmap ((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) ) (app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z))))) (replace_Znth (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) (1) (bitmap_2)) ) ”
  &&  emp
).

Definition solver_entail_wit_6_3 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment_2: (@list Z)) (bitmap_2: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products_2: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : (((Znth (j - 0 ) products_before_append 0) * v ) = x_pre)) (PreH2 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap_2 0) <> 0)) (PreH3 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH4 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH5 : (reaches <= INT_MAX)) (PreH6 : (j <= INT_MAX)) (PreH7 : (count <= INT_MAX)) (PreH8 : (old <= INT_MAX)) (PreH9 : (segments <= INT_MAX)) (PreH10 : (v <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (reaches >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (count >= INT_MIN)) (PreH16 : (old >= INT_MIN)) (PreH17 : (segments >= INT_MIN)) (PreH18 : (v >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH22 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH23 : (j < old)) (PreH24 : (n_pre = (Zlength (values)))) (PreH25 : (2 <= x_pre)) (PreH26 : (x_pre <= 100000)) (PreH27 : (1 <= (Zlength (values)))) (PreH28 : ((Zlength (values)) <= 100000)) (PreH29 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH30 : (Pre x_pre values )) (PreH31 : (0 <= i)) (PreH32 : (i < n_pre)) (PreH33 : (v = (Znth i values 0))) (PreH34 : (1 <= v)) (PreH35 : (v <= x_pre)) (PreH36 : ((x_pre % ( v ) ) = 0)) (PreH37 : (1 <= segments)) (PreH38 : (segments <= (i + 1 ))) (PreH39 : (old = (Zlength (base_products_2)))) (PreH40 : (base_products_2 = (sublist (0) (old) (products_before_append)))) (PreH41 : (1 <= old)) (PreH42 : (old <= count)) (PreH43 : (count <= x_pre)) (PreH44 : (0 <= j)) (PreH45 : (j <= old)) (PreH46 : (count = (Zlength (products_before_append)))) (PreH47 : (reaches = 1)) (PreH48 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH49 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH50 : (ValuableOuterState x_pre values i segments base_products_2 )) (PreH51 : (ValuableForcedHistory x_pre values i segments base_products_2 )) (PreH52 : (ValuableAlignedHistory x_pre values i segments base_products_2 )) (PreH53 : (ValuableClosureState x_pre segment_2 v base_products_2 j products_before_append reaches )) (PreH54 : (ValuableBitmap x_pre products_before_append bitmap_2 )),
  (UCharArray.full used (x_pre + 1 ) bitmap_2 )
  **  (IntArray.seg products_buf 0 count products_before_append )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
|--
  EX (segment: (@list Z)) (bitmap: (@list Z)) (products: (@list Z)) (base_products: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products))) ”
  &&  “ (1 <= old) ”
  &&  “ (old <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= old) ”
  &&  “ (count = (Zlength (products))) ”
  &&  “ (1 = 1) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products (j + 1 ) products 1 ) ”
  &&  “ (ValuableBitmap x_pre products bitmap ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment_2: (@list Z)) (bitmap_2: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products_2: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : (((Znth (j - 0 ) products_before_append 0) * v ) = x_pre)) (PreH2 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap_2 0) <> 0)) (PreH3 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH4 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH5 : (reaches <= INT_MAX)) (PreH6 : (j <= INT_MAX)) (PreH7 : (count <= INT_MAX)) (PreH8 : (old <= INT_MAX)) (PreH9 : (segments <= INT_MAX)) (PreH10 : (v <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (reaches >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (count >= INT_MIN)) (PreH16 : (old >= INT_MIN)) (PreH17 : (segments >= INT_MIN)) (PreH18 : (v >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH22 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH23 : (j < old)) (PreH24 : (n_pre = (Zlength (values)))) (PreH25 : (2 <= x_pre)) (PreH26 : (x_pre <= 100000)) (PreH27 : (1 <= (Zlength (values)))) (PreH28 : ((Zlength (values)) <= 100000)) (PreH29 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH30 : (Pre x_pre values )) (PreH31 : (0 <= i)) (PreH32 : (i < n_pre)) (PreH33 : (v = (Znth i values 0))) (PreH34 : (1 <= v)) (PreH35 : (v <= x_pre)) (PreH36 : ((x_pre % ( v ) ) = 0)) (PreH37 : (1 <= segments)) (PreH38 : (segments <= (i + 1 ))) (PreH39 : (old = (Zlength (base_products_2)))) (PreH40 : (base_products_2 = (sublist (0) (old) (products_before_append)))) (PreH41 : (1 <= old)) (PreH42 : (old <= count)) (PreH43 : (count <= x_pre)) (PreH44 : (0 <= j)) (PreH45 : (j <= old)) (PreH46 : (count = (Zlength (products_before_append)))) (PreH47 : (reaches = 1)) (PreH48 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH49 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH50 : (ValuableOuterState x_pre values i segments base_products_2 )) (PreH51 : (ValuableForcedHistory x_pre values i segments base_products_2 )) (PreH52 : (ValuableAlignedHistory x_pre values i segments base_products_2 )) (PreH53 : (ValuableClosureState x_pre segment_2 v base_products_2 j products_before_append reaches )) (PreH54 : (ValuableBitmap x_pre products_before_append bitmap_2 )),
  TT && emp 
|--
  EX (segment: (@list Z)),
  “ ((Zlength ((sublist (0) (old) (products_before_append)))) = (Zlength ((sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append))))) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (Zlength ((sublist (0) (old) (products_before_append))))) ”
  &&  “ (ValuableOuterState ((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) ) values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append)) ) ”
  &&  “ (ValuableForcedHistory ((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) ) values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append)) ) ”
  &&  “ (ValuableAlignedHistory ((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) ) values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append)) ) ”
  &&  “ (ValuableClosureState ((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) ) segment (Znth i values 0) (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append)) (j + 1 ) products_before_append 1 ) ”
  &&  emp
).

Definition solver_entail_wit_6_4 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment_2: (@list Z)) (bitmap_2: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products_2: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : (((Znth (j - 0 ) products_before_append 0) * v ) = x_pre)) (PreH2 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap_2 0) <> 0)) (PreH3 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH4 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH5 : (reaches <= INT_MAX)) (PreH6 : (j <= INT_MAX)) (PreH7 : (count <= INT_MAX)) (PreH8 : (old <= INT_MAX)) (PreH9 : (segments <= INT_MAX)) (PreH10 : (v <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (reaches >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (count >= INT_MIN)) (PreH16 : (old >= INT_MIN)) (PreH17 : (segments >= INT_MIN)) (PreH18 : (v >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH22 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH23 : (j < old)) (PreH24 : (n_pre = (Zlength (values)))) (PreH25 : (2 <= x_pre)) (PreH26 : (x_pre <= 100000)) (PreH27 : (1 <= (Zlength (values)))) (PreH28 : ((Zlength (values)) <= 100000)) (PreH29 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH30 : (Pre x_pre values )) (PreH31 : (0 <= i)) (PreH32 : (i < n_pre)) (PreH33 : (v = (Znth i values 0))) (PreH34 : (1 <= v)) (PreH35 : (v <= x_pre)) (PreH36 : ((x_pre % ( v ) ) = 0)) (PreH37 : (1 <= segments)) (PreH38 : (segments <= (i + 1 ))) (PreH39 : (old = (Zlength (base_products_2)))) (PreH40 : (base_products_2 = (sublist (0) (old) (products_before_append)))) (PreH41 : (1 <= old)) (PreH42 : (old <= count)) (PreH43 : (count <= x_pre)) (PreH44 : (0 <= j)) (PreH45 : (j <= old)) (PreH46 : (count = (Zlength (products_before_append)))) (PreH47 : (reaches = 0)) (PreH48 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH49 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH50 : (ValuableOuterState x_pre values i segments base_products_2 )) (PreH51 : (ValuableForcedHistory x_pre values i segments base_products_2 )) (PreH52 : (ValuableAlignedHistory x_pre values i segments base_products_2 )) (PreH53 : (ValuableClosureState x_pre segment_2 v base_products_2 j products_before_append reaches )) (PreH54 : (ValuableBitmap x_pre products_before_append bitmap_2 )),
  (UCharArray.full used (x_pre + 1 ) bitmap_2 )
  **  (IntArray.seg products_buf 0 count products_before_append )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
|--
  EX (segment: (@list Z)) (bitmap: (@list Z)) (products: (@list Z)) (base_products: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products))) ”
  &&  “ (1 <= old) ”
  &&  “ (old <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= old) ”
  &&  “ (count = (Zlength (products))) ”
  &&  “ (1 = 1) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products (j + 1 ) products 1 ) ”
  &&  “ (ValuableBitmap x_pre products bitmap ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment_2: (@list Z)) (bitmap_2: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products_2: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : (((Znth (j - 0 ) products_before_append 0) * v ) = x_pre)) (PreH2 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap_2 0) <> 0)) (PreH3 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH4 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH5 : (reaches <= INT_MAX)) (PreH6 : (j <= INT_MAX)) (PreH7 : (count <= INT_MAX)) (PreH8 : (old <= INT_MAX)) (PreH9 : (segments <= INT_MAX)) (PreH10 : (v <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (reaches >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (count >= INT_MIN)) (PreH16 : (old >= INT_MIN)) (PreH17 : (segments >= INT_MIN)) (PreH18 : (v >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH22 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH23 : (j < old)) (PreH24 : (n_pre = (Zlength (values)))) (PreH25 : (2 <= x_pre)) (PreH26 : (x_pre <= 100000)) (PreH27 : (1 <= (Zlength (values)))) (PreH28 : ((Zlength (values)) <= 100000)) (PreH29 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH30 : (Pre x_pre values )) (PreH31 : (0 <= i)) (PreH32 : (i < n_pre)) (PreH33 : (v = (Znth i values 0))) (PreH34 : (1 <= v)) (PreH35 : (v <= x_pre)) (PreH36 : ((x_pre % ( v ) ) = 0)) (PreH37 : (1 <= segments)) (PreH38 : (segments <= (i + 1 ))) (PreH39 : (old = (Zlength (base_products_2)))) (PreH40 : (base_products_2 = (sublist (0) (old) (products_before_append)))) (PreH41 : (1 <= old)) (PreH42 : (old <= count)) (PreH43 : (count <= x_pre)) (PreH44 : (0 <= j)) (PreH45 : (j <= old)) (PreH46 : (count = (Zlength (products_before_append)))) (PreH47 : (reaches = 0)) (PreH48 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH49 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH50 : (ValuableOuterState x_pre values i segments base_products_2 )) (PreH51 : (ValuableForcedHistory x_pre values i segments base_products_2 )) (PreH52 : (ValuableAlignedHistory x_pre values i segments base_products_2 )) (PreH53 : (ValuableClosureState x_pre segment_2 v base_products_2 j products_before_append reaches )) (PreH54 : (ValuableBitmap x_pre products_before_append bitmap_2 )),
  TT && emp 
|--
  EX (segment: (@list Z)),
  “ ((Zlength ((sublist (0) (old) (products_before_append)))) = (Zlength ((sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append))))) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (Zlength ((sublist (0) (old) (products_before_append))))) ”
  &&  “ (ValuableOuterState ((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) ) values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append)) ) ”
  &&  “ (ValuableForcedHistory ((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) ) values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append)) ) ”
  &&  “ (ValuableAlignedHistory ((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) ) values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append)) ) ”
  &&  “ (ValuableClosureState ((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) ) segment (Znth i values 0) (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append)) (j + 1 ) products_before_append 1 ) ”
  &&  emp
).

Definition solver_entail_wit_6_5 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment_2: (@list Z)) (bitmap_2: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products_2: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : (((Znth (j - 0 ) products_before_append 0) * v ) <> x_pre)) (PreH2 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap_2 0) = 0)) (PreH3 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH4 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH5 : (reaches <= INT_MAX)) (PreH6 : (j <= INT_MAX)) (PreH7 : (count <= INT_MAX)) (PreH8 : (old <= INT_MAX)) (PreH9 : (segments <= INT_MAX)) (PreH10 : (v <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (reaches >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (count >= INT_MIN)) (PreH16 : (old >= INT_MIN)) (PreH17 : (segments >= INT_MIN)) (PreH18 : (v >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH22 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH23 : (j < old)) (PreH24 : (n_pre = (Zlength (values)))) (PreH25 : (2 <= x_pre)) (PreH26 : (x_pre <= 100000)) (PreH27 : (1 <= (Zlength (values)))) (PreH28 : ((Zlength (values)) <= 100000)) (PreH29 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH30 : (Pre x_pre values )) (PreH31 : (0 <= i)) (PreH32 : (i < n_pre)) (PreH33 : (v = (Znth i values 0))) (PreH34 : (1 <= v)) (PreH35 : (v <= x_pre)) (PreH36 : ((x_pre % ( v ) ) = 0)) (PreH37 : (1 <= segments)) (PreH38 : (segments <= (i + 1 ))) (PreH39 : (old = (Zlength (base_products_2)))) (PreH40 : (base_products_2 = (sublist (0) (old) (products_before_append)))) (PreH41 : (1 <= old)) (PreH42 : (old <= count)) (PreH43 : (count <= x_pre)) (PreH44 : (0 <= j)) (PreH45 : (j <= old)) (PreH46 : (count = (Zlength (products_before_append)))) (PreH47 : (reaches = 1)) (PreH48 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH49 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH50 : (ValuableOuterState x_pre values i segments base_products_2 )) (PreH51 : (ValuableForcedHistory x_pre values i segments base_products_2 )) (PreH52 : (ValuableAlignedHistory x_pre values i segments base_products_2 )) (PreH53 : (ValuableClosureState x_pre segment_2 v base_products_2 j products_before_append reaches )) (PreH54 : (ValuableBitmap x_pre products_before_append bitmap_2 )),
  (IntArray.seg products_buf 0 (count + 1 ) (app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * v )) ((@nil Z))))) )
  **  (IntArray.undef_seg products_buf (count + 1 ) (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) (replace_Znth (((Znth (j - 0 ) products_before_append 0) * v )) (1) (bitmap_2)) )
  **  (IntArray.full a_pre n_pre values )
|--
  EX (segment: (@list Z)) (bitmap: (@list Z)) (products: (@list Z)) (base_products: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products))) ”
  &&  “ (1 <= old) ”
  &&  “ (old <= (count + 1 )) ”
  &&  “ ((count + 1 ) <= x_pre) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= old) ”
  &&  “ ((count + 1 ) = (Zlength (products))) ”
  &&  “ (reaches = 1) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (count + 1 ))) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products (j + 1 ) products reaches ) ”
  &&  “ (ValuableBitmap x_pre products bitmap ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 (count + 1 ) products )
  **  (IntArray.undef_seg products_buf (count + 1 ) (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment_2: (@list Z)) (bitmap_2: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products_2: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : (((Znth (j - 0 ) products_before_append 0) * v ) <> x_pre)) (PreH2 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap_2 0) = 0)) (PreH3 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH4 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH5 : (reaches <= INT_MAX)) (PreH6 : (j <= INT_MAX)) (PreH7 : (count <= INT_MAX)) (PreH8 : (old <= INT_MAX)) (PreH9 : (segments <= INT_MAX)) (PreH10 : (v <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (reaches >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (count >= INT_MIN)) (PreH16 : (old >= INT_MIN)) (PreH17 : (segments >= INT_MIN)) (PreH18 : (v >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH22 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH23 : (j < old)) (PreH24 : (n_pre = (Zlength (values)))) (PreH25 : (2 <= x_pre)) (PreH26 : (x_pre <= 100000)) (PreH27 : (1 <= (Zlength (values)))) (PreH28 : ((Zlength (values)) <= 100000)) (PreH29 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH30 : (Pre x_pre values )) (PreH31 : (0 <= i)) (PreH32 : (i < n_pre)) (PreH33 : (v = (Znth i values 0))) (PreH34 : (1 <= v)) (PreH35 : (v <= x_pre)) (PreH36 : ((x_pre % ( v ) ) = 0)) (PreH37 : (1 <= segments)) (PreH38 : (segments <= (i + 1 ))) (PreH39 : (old = (Zlength (base_products_2)))) (PreH40 : (base_products_2 = (sublist (0) (old) (products_before_append)))) (PreH41 : (1 <= old)) (PreH42 : (old <= count)) (PreH43 : (count <= x_pre)) (PreH44 : (0 <= j)) (PreH45 : (j <= old)) (PreH46 : (count = (Zlength (products_before_append)))) (PreH47 : (reaches = 1)) (PreH48 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH49 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH50 : (ValuableOuterState x_pre values i segments base_products_2 )) (PreH51 : (ValuableForcedHistory x_pre values i segments base_products_2 )) (PreH52 : (ValuableAlignedHistory x_pre values i segments base_products_2 )) (PreH53 : (ValuableClosureState x_pre segment_2 v base_products_2 j products_before_append reaches )) (PreH54 : (ValuableBitmap x_pre products_before_append bitmap_2 )),
  TT && emp 
|--
  EX (segment: (@list Z)),
  “ ((Zlength ((sublist (0) (old) (products_before_append)))) = (Zlength ((sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) ((app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z)))))))))) ”
  &&  “ ((Zlength ((sublist (0) (old) (products_before_append)))) <= ((Zlength (products_before_append)) + 1 )) ”
  &&  “ (((Zlength (products_before_append)) + 1 ) <= x_pre) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (Zlength ((sublist (0) (old) (products_before_append))))) ”
  &&  “ (((Zlength (products_before_append)) + 1 ) = (Zlength ((app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z)))))))) ”
  &&  “ ((Zlength ((replace_Znth (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) (1) (bitmap_2)))) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < ((Zlength (products_before_append)) + 1 ))) -> ((1 <= (Znth k_2 (app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z))))) 0)) /\ ((Znth k_2 (app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z))))) 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) ((app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z))))))) ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) ((app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z))))))) ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) ((app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z))))))) ) ”
  &&  “ (ValuableClosureState x_pre segment (Znth i values 0) (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) ((app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z))))))) (j + 1 ) (app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z))))) 1 ) ”
  &&  “ (ValuableBitmap x_pre (app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z))))) (replace_Znth (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) (1) (bitmap_2)) ) ”
  &&  emp
).

Definition solver_entail_wit_6_6 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment_2: (@list Z)) (bitmap_2: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products_2: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : (((Znth (j - 0 ) products_before_append 0) * v ) <> x_pre)) (PreH2 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap_2 0) = 0)) (PreH3 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH4 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH5 : (reaches <= INT_MAX)) (PreH6 : (j <= INT_MAX)) (PreH7 : (count <= INT_MAX)) (PreH8 : (old <= INT_MAX)) (PreH9 : (segments <= INT_MAX)) (PreH10 : (v <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (reaches >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (count >= INT_MIN)) (PreH16 : (old >= INT_MIN)) (PreH17 : (segments >= INT_MIN)) (PreH18 : (v >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH22 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH23 : (j < old)) (PreH24 : (n_pre = (Zlength (values)))) (PreH25 : (2 <= x_pre)) (PreH26 : (x_pre <= 100000)) (PreH27 : (1 <= (Zlength (values)))) (PreH28 : ((Zlength (values)) <= 100000)) (PreH29 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH30 : (Pre x_pre values )) (PreH31 : (0 <= i)) (PreH32 : (i < n_pre)) (PreH33 : (v = (Znth i values 0))) (PreH34 : (1 <= v)) (PreH35 : (v <= x_pre)) (PreH36 : ((x_pre % ( v ) ) = 0)) (PreH37 : (1 <= segments)) (PreH38 : (segments <= (i + 1 ))) (PreH39 : (old = (Zlength (base_products_2)))) (PreH40 : (base_products_2 = (sublist (0) (old) (products_before_append)))) (PreH41 : (1 <= old)) (PreH42 : (old <= count)) (PreH43 : (count <= x_pre)) (PreH44 : (0 <= j)) (PreH45 : (j <= old)) (PreH46 : (count = (Zlength (products_before_append)))) (PreH47 : (reaches = 0)) (PreH48 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH49 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH50 : (ValuableOuterState x_pre values i segments base_products_2 )) (PreH51 : (ValuableForcedHistory x_pre values i segments base_products_2 )) (PreH52 : (ValuableAlignedHistory x_pre values i segments base_products_2 )) (PreH53 : (ValuableClosureState x_pre segment_2 v base_products_2 j products_before_append reaches )) (PreH54 : (ValuableBitmap x_pre products_before_append bitmap_2 )),
  (IntArray.seg products_buf 0 (count + 1 ) (app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * v )) ((@nil Z))))) )
  **  (IntArray.undef_seg products_buf (count + 1 ) (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) (replace_Znth (((Znth (j - 0 ) products_before_append 0) * v )) (1) (bitmap_2)) )
  **  (IntArray.full a_pre n_pre values )
|--
  EX (segment: (@list Z)) (bitmap: (@list Z)) (products: (@list Z)) (base_products: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products))) ”
  &&  “ (1 <= old) ”
  &&  “ (old <= (count + 1 )) ”
  &&  “ ((count + 1 ) <= x_pre) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= old) ”
  &&  “ ((count + 1 ) = (Zlength (products))) ”
  &&  “ (reaches = 0) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (count + 1 ))) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products (j + 1 ) products reaches ) ”
  &&  “ (ValuableBitmap x_pre products bitmap ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 (count + 1 ) products )
  **  (IntArray.undef_seg products_buf (count + 1 ) (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment_2: (@list Z)) (bitmap_2: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products_2: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : (((Znth (j - 0 ) products_before_append 0) * v ) <> x_pre)) (PreH2 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap_2 0) = 0)) (PreH3 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH4 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH5 : (reaches <= INT_MAX)) (PreH6 : (j <= INT_MAX)) (PreH7 : (count <= INT_MAX)) (PreH8 : (old <= INT_MAX)) (PreH9 : (segments <= INT_MAX)) (PreH10 : (v <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (reaches >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (count >= INT_MIN)) (PreH16 : (old >= INT_MIN)) (PreH17 : (segments >= INT_MIN)) (PreH18 : (v >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH22 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH23 : (j < old)) (PreH24 : (n_pre = (Zlength (values)))) (PreH25 : (2 <= x_pre)) (PreH26 : (x_pre <= 100000)) (PreH27 : (1 <= (Zlength (values)))) (PreH28 : ((Zlength (values)) <= 100000)) (PreH29 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH30 : (Pre x_pre values )) (PreH31 : (0 <= i)) (PreH32 : (i < n_pre)) (PreH33 : (v = (Znth i values 0))) (PreH34 : (1 <= v)) (PreH35 : (v <= x_pre)) (PreH36 : ((x_pre % ( v ) ) = 0)) (PreH37 : (1 <= segments)) (PreH38 : (segments <= (i + 1 ))) (PreH39 : (old = (Zlength (base_products_2)))) (PreH40 : (base_products_2 = (sublist (0) (old) (products_before_append)))) (PreH41 : (1 <= old)) (PreH42 : (old <= count)) (PreH43 : (count <= x_pre)) (PreH44 : (0 <= j)) (PreH45 : (j <= old)) (PreH46 : (count = (Zlength (products_before_append)))) (PreH47 : (reaches = 0)) (PreH48 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH49 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH50 : (ValuableOuterState x_pre values i segments base_products_2 )) (PreH51 : (ValuableForcedHistory x_pre values i segments base_products_2 )) (PreH52 : (ValuableAlignedHistory x_pre values i segments base_products_2 )) (PreH53 : (ValuableClosureState x_pre segment_2 v base_products_2 j products_before_append reaches )) (PreH54 : (ValuableBitmap x_pre products_before_append bitmap_2 )),
  TT && emp 
|--
  EX (segment: (@list Z)),
  “ ((Zlength ((sublist (0) (old) (products_before_append)))) = (Zlength ((sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) ((app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z)))))))))) ”
  &&  “ ((Zlength ((sublist (0) (old) (products_before_append)))) <= ((Zlength (products_before_append)) + 1 )) ”
  &&  “ (((Zlength (products_before_append)) + 1 ) <= x_pre) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (Zlength ((sublist (0) (old) (products_before_append))))) ”
  &&  “ (((Zlength (products_before_append)) + 1 ) = (Zlength ((app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z)))))))) ”
  &&  “ ((Zlength ((replace_Znth (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) (1) (bitmap_2)))) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < ((Zlength (products_before_append)) + 1 ))) -> ((1 <= (Znth k_2 (app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z))))) 0)) /\ ((Znth k_2 (app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z))))) 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) ((app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z))))))) ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) ((app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z))))))) ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) ((app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z))))))) ) ”
  &&  “ (ValuableClosureState x_pre segment (Znth i values 0) (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) ((app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z))))))) (j + 1 ) (app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z))))) 0 ) ”
  &&  “ (ValuableBitmap x_pre (app (products_before_append) ((cons (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) ((@nil Z))))) (replace_Znth (((Znth (j - 0 ) products_before_append 0) * (Znth i values 0) )) (1) (bitmap_2)) ) ”
  &&  emp
).

Definition solver_entail_wit_6_7 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment_2: (@list Z)) (bitmap_2: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products_2: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : (((Znth (j - 0 ) products_before_append 0) * v ) <> x_pre)) (PreH2 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap_2 0) <> 0)) (PreH3 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH4 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH5 : (reaches <= INT_MAX)) (PreH6 : (j <= INT_MAX)) (PreH7 : (count <= INT_MAX)) (PreH8 : (old <= INT_MAX)) (PreH9 : (segments <= INT_MAX)) (PreH10 : (v <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (reaches >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (count >= INT_MIN)) (PreH16 : (old >= INT_MIN)) (PreH17 : (segments >= INT_MIN)) (PreH18 : (v >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH22 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH23 : (j < old)) (PreH24 : (n_pre = (Zlength (values)))) (PreH25 : (2 <= x_pre)) (PreH26 : (x_pre <= 100000)) (PreH27 : (1 <= (Zlength (values)))) (PreH28 : ((Zlength (values)) <= 100000)) (PreH29 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH30 : (Pre x_pre values )) (PreH31 : (0 <= i)) (PreH32 : (i < n_pre)) (PreH33 : (v = (Znth i values 0))) (PreH34 : (1 <= v)) (PreH35 : (v <= x_pre)) (PreH36 : ((x_pre % ( v ) ) = 0)) (PreH37 : (1 <= segments)) (PreH38 : (segments <= (i + 1 ))) (PreH39 : (old = (Zlength (base_products_2)))) (PreH40 : (base_products_2 = (sublist (0) (old) (products_before_append)))) (PreH41 : (1 <= old)) (PreH42 : (old <= count)) (PreH43 : (count <= x_pre)) (PreH44 : (0 <= j)) (PreH45 : (j <= old)) (PreH46 : (count = (Zlength (products_before_append)))) (PreH47 : (reaches = 1)) (PreH48 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH49 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH50 : (ValuableOuterState x_pre values i segments base_products_2 )) (PreH51 : (ValuableForcedHistory x_pre values i segments base_products_2 )) (PreH52 : (ValuableAlignedHistory x_pre values i segments base_products_2 )) (PreH53 : (ValuableClosureState x_pre segment_2 v base_products_2 j products_before_append reaches )) (PreH54 : (ValuableBitmap x_pre products_before_append bitmap_2 )),
  (UCharArray.full used (x_pre + 1 ) bitmap_2 )
  **  (IntArray.seg products_buf 0 count products_before_append )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
|--
  EX (segment: (@list Z)) (bitmap: (@list Z)) (products: (@list Z)) (base_products: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products))) ”
  &&  “ (1 <= old) ”
  &&  “ (old <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= old) ”
  &&  “ (count = (Zlength (products))) ”
  &&  “ (reaches = 1) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products (j + 1 ) products reaches ) ”
  &&  “ (ValuableBitmap x_pre products bitmap ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment_2: (@list Z)) (bitmap_2: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products_2: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : (((Znth (j - 0 ) products_before_append 0) * v ) <> x_pre)) (PreH2 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap_2 0) <> 0)) (PreH3 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH4 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH5 : (reaches <= INT_MAX)) (PreH6 : (j <= INT_MAX)) (PreH7 : (count <= INT_MAX)) (PreH8 : (old <= INT_MAX)) (PreH9 : (segments <= INT_MAX)) (PreH10 : (v <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (reaches >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (count >= INT_MIN)) (PreH16 : (old >= INT_MIN)) (PreH17 : (segments >= INT_MIN)) (PreH18 : (v >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH22 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH23 : (j < old)) (PreH24 : (n_pre = (Zlength (values)))) (PreH25 : (2 <= x_pre)) (PreH26 : (x_pre <= 100000)) (PreH27 : (1 <= (Zlength (values)))) (PreH28 : ((Zlength (values)) <= 100000)) (PreH29 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH30 : (Pre x_pre values )) (PreH31 : (0 <= i)) (PreH32 : (i < n_pre)) (PreH33 : (v = (Znth i values 0))) (PreH34 : (1 <= v)) (PreH35 : (v <= x_pre)) (PreH36 : ((x_pre % ( v ) ) = 0)) (PreH37 : (1 <= segments)) (PreH38 : (segments <= (i + 1 ))) (PreH39 : (old = (Zlength (base_products_2)))) (PreH40 : (base_products_2 = (sublist (0) (old) (products_before_append)))) (PreH41 : (1 <= old)) (PreH42 : (old <= count)) (PreH43 : (count <= x_pre)) (PreH44 : (0 <= j)) (PreH45 : (j <= old)) (PreH46 : (count = (Zlength (products_before_append)))) (PreH47 : (reaches = 1)) (PreH48 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH49 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH50 : (ValuableOuterState x_pre values i segments base_products_2 )) (PreH51 : (ValuableForcedHistory x_pre values i segments base_products_2 )) (PreH52 : (ValuableAlignedHistory x_pre values i segments base_products_2 )) (PreH53 : (ValuableClosureState x_pre segment_2 v base_products_2 j products_before_append reaches )) (PreH54 : (ValuableBitmap x_pre products_before_append bitmap_2 )),
  TT && emp 
|--
  EX (segment: (@list Z)),
  “ ((Zlength ((sublist (0) (old) (products_before_append)))) = (Zlength ((sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append))))) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (Zlength ((sublist (0) (old) (products_before_append))))) ”
  &&  “ (ValuableOuterState x_pre values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append)) ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append)) ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append)) ) ”
  &&  “ (ValuableClosureState x_pre segment (Znth i values 0) (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append)) (j + 1 ) products_before_append 1 ) ”
  &&  emp
).

Definition solver_entail_wit_6_8 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment_2: (@list Z)) (bitmap_2: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products_2: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : (((Znth (j - 0 ) products_before_append 0) * v ) <> x_pre)) (PreH2 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap_2 0) <> 0)) (PreH3 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH4 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH5 : (reaches <= INT_MAX)) (PreH6 : (j <= INT_MAX)) (PreH7 : (count <= INT_MAX)) (PreH8 : (old <= INT_MAX)) (PreH9 : (segments <= INT_MAX)) (PreH10 : (v <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (reaches >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (count >= INT_MIN)) (PreH16 : (old >= INT_MIN)) (PreH17 : (segments >= INT_MIN)) (PreH18 : (v >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH22 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH23 : (j < old)) (PreH24 : (n_pre = (Zlength (values)))) (PreH25 : (2 <= x_pre)) (PreH26 : (x_pre <= 100000)) (PreH27 : (1 <= (Zlength (values)))) (PreH28 : ((Zlength (values)) <= 100000)) (PreH29 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH30 : (Pre x_pre values )) (PreH31 : (0 <= i)) (PreH32 : (i < n_pre)) (PreH33 : (v = (Znth i values 0))) (PreH34 : (1 <= v)) (PreH35 : (v <= x_pre)) (PreH36 : ((x_pre % ( v ) ) = 0)) (PreH37 : (1 <= segments)) (PreH38 : (segments <= (i + 1 ))) (PreH39 : (old = (Zlength (base_products_2)))) (PreH40 : (base_products_2 = (sublist (0) (old) (products_before_append)))) (PreH41 : (1 <= old)) (PreH42 : (old <= count)) (PreH43 : (count <= x_pre)) (PreH44 : (0 <= j)) (PreH45 : (j <= old)) (PreH46 : (count = (Zlength (products_before_append)))) (PreH47 : (reaches = 0)) (PreH48 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH49 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH50 : (ValuableOuterState x_pre values i segments base_products_2 )) (PreH51 : (ValuableForcedHistory x_pre values i segments base_products_2 )) (PreH52 : (ValuableAlignedHistory x_pre values i segments base_products_2 )) (PreH53 : (ValuableClosureState x_pre segment_2 v base_products_2 j products_before_append reaches )) (PreH54 : (ValuableBitmap x_pre products_before_append bitmap_2 )),
  (UCharArray.full used (x_pre + 1 ) bitmap_2 )
  **  (IntArray.seg products_buf 0 count products_before_append )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
|--
  EX (segment: (@list Z)) (bitmap: (@list Z)) (products: (@list Z)) (base_products: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products))) ”
  &&  “ (1 <= old) ”
  &&  “ (old <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= old) ”
  &&  “ (count = (Zlength (products))) ”
  &&  “ (reaches = 0) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products (j + 1 ) products reaches ) ”
  &&  “ (ValuableBitmap x_pre products bitmap ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment_2: (@list Z)) (bitmap_2: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products_2: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : (((Znth (j - 0 ) products_before_append 0) * v ) <> x_pre)) (PreH2 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap_2 0) <> 0)) (PreH3 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH4 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH5 : (reaches <= INT_MAX)) (PreH6 : (j <= INT_MAX)) (PreH7 : (count <= INT_MAX)) (PreH8 : (old <= INT_MAX)) (PreH9 : (segments <= INT_MAX)) (PreH10 : (v <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (reaches >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (count >= INT_MIN)) (PreH16 : (old >= INT_MIN)) (PreH17 : (segments >= INT_MIN)) (PreH18 : (v >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH22 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH23 : (j < old)) (PreH24 : (n_pre = (Zlength (values)))) (PreH25 : (2 <= x_pre)) (PreH26 : (x_pre <= 100000)) (PreH27 : (1 <= (Zlength (values)))) (PreH28 : ((Zlength (values)) <= 100000)) (PreH29 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH30 : (Pre x_pre values )) (PreH31 : (0 <= i)) (PreH32 : (i < n_pre)) (PreH33 : (v = (Znth i values 0))) (PreH34 : (1 <= v)) (PreH35 : (v <= x_pre)) (PreH36 : ((x_pre % ( v ) ) = 0)) (PreH37 : (1 <= segments)) (PreH38 : (segments <= (i + 1 ))) (PreH39 : (old = (Zlength (base_products_2)))) (PreH40 : (base_products_2 = (sublist (0) (old) (products_before_append)))) (PreH41 : (1 <= old)) (PreH42 : (old <= count)) (PreH43 : (count <= x_pre)) (PreH44 : (0 <= j)) (PreH45 : (j <= old)) (PreH46 : (count = (Zlength (products_before_append)))) (PreH47 : (reaches = 0)) (PreH48 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH49 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH50 : (ValuableOuterState x_pre values i segments base_products_2 )) (PreH51 : (ValuableForcedHistory x_pre values i segments base_products_2 )) (PreH52 : (ValuableAlignedHistory x_pre values i segments base_products_2 )) (PreH53 : (ValuableClosureState x_pre segment_2 v base_products_2 j products_before_append reaches )) (PreH54 : (ValuableBitmap x_pre products_before_append bitmap_2 )),
  TT && emp 
|--
  EX (segment: (@list Z)),
  “ ((Zlength ((sublist (0) (old) (products_before_append)))) = (Zlength ((sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append))))) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (Zlength ((sublist (0) (old) (products_before_append))))) ”
  &&  “ (ValuableOuterState x_pre values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append)) ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append)) ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append)) ) ”
  &&  “ (ValuableClosureState x_pre segment (Znth i values 0) (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append)) (j + 1 ) products_before_append 0 ) ”
  &&  emp
).

Definition solver_entail_wit_6_9 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment_2: (@list Z)) (bitmap_2: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products_2: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((Znth (j - 0 ) products_before_append 0) > (x_pre ÷ v ))) (PreH2 : (j < old)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 100000)) (PreH6 : (1 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH9 : (Pre x_pre values )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (v = (Znth i values 0))) (PreH13 : (1 <= v)) (PreH14 : (v <= x_pre)) (PreH15 : ((x_pre % ( v ) ) = 0)) (PreH16 : (1 <= segments)) (PreH17 : (segments <= (i + 1 ))) (PreH18 : (old = (Zlength (base_products_2)))) (PreH19 : (base_products_2 = (sublist (0) (old) (products_before_append)))) (PreH20 : (1 <= old)) (PreH21 : (old <= count)) (PreH22 : (count <= x_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= old)) (PreH25 : (count = (Zlength (products_before_append)))) (PreH26 : (reaches = 0)) (PreH27 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH28 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH29 : (ValuableOuterState x_pre values i segments base_products_2 )) (PreH30 : (ValuableForcedHistory x_pre values i segments base_products_2 )) (PreH31 : (ValuableAlignedHistory x_pre values i segments base_products_2 )) (PreH32 : (ValuableClosureState x_pre segment_2 v base_products_2 j products_before_append reaches )) (PreH33 : (ValuableBitmap x_pre products_before_append bitmap_2 )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap_2 )
|--
  EX (segment: (@list Z)) (bitmap: (@list Z)) (products: (@list Z)) (base_products: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products))) ”
  &&  “ (1 <= old) ”
  &&  “ (old <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= old) ”
  &&  “ (count = (Zlength (products))) ”
  &&  “ (reaches = 0) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products (j + 1 ) products reaches ) ”
  &&  “ (ValuableBitmap x_pre products bitmap ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment_2: (@list Z)) (bitmap_2: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products_2: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((Znth (j - 0 ) products_before_append 0) > (x_pre ÷ v ))) (PreH2 : (j < old)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 100000)) (PreH6 : (1 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH9 : (Pre x_pre values )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (v = (Znth i values 0))) (PreH13 : (1 <= v)) (PreH14 : (v <= x_pre)) (PreH15 : ((x_pre % ( v ) ) = 0)) (PreH16 : (1 <= segments)) (PreH17 : (segments <= (i + 1 ))) (PreH18 : (old = (Zlength (base_products_2)))) (PreH19 : (base_products_2 = (sublist (0) (old) (products_before_append)))) (PreH20 : (1 <= old)) (PreH21 : (old <= count)) (PreH22 : (count <= x_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= old)) (PreH25 : (count = (Zlength (products_before_append)))) (PreH26 : (reaches = 0)) (PreH27 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH28 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH29 : (ValuableOuterState x_pre values i segments base_products_2 )) (PreH30 : (ValuableForcedHistory x_pre values i segments base_products_2 )) (PreH31 : (ValuableAlignedHistory x_pre values i segments base_products_2 )) (PreH32 : (ValuableClosureState x_pre segment_2 v base_products_2 j products_before_append reaches )) (PreH33 : (ValuableBitmap x_pre products_before_append bitmap_2 )),
  TT && emp 
|--
  EX (segment: (@list Z)),
  “ ((Zlength ((sublist (0) (old) (products_before_append)))) = (Zlength ((sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append))))) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (Zlength ((sublist (0) (old) (products_before_append))))) ”
  &&  “ (ValuableOuterState x_pre values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append)) ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append)) ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append)) ) ”
  &&  “ (ValuableClosureState x_pre segment (Znth i values 0) (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append)) (j + 1 ) products_before_append 0 ) ”
  &&  emp
).

Definition solver_entail_wit_6_10 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment_2: (@list Z)) (bitmap_2: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products_2: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((Znth (j - 0 ) products_before_append 0) > (x_pre ÷ v ))) (PreH2 : (j < old)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 100000)) (PreH6 : (1 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH9 : (Pre x_pre values )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (v = (Znth i values 0))) (PreH13 : (1 <= v)) (PreH14 : (v <= x_pre)) (PreH15 : ((x_pre % ( v ) ) = 0)) (PreH16 : (1 <= segments)) (PreH17 : (segments <= (i + 1 ))) (PreH18 : (old = (Zlength (base_products_2)))) (PreH19 : (base_products_2 = (sublist (0) (old) (products_before_append)))) (PreH20 : (1 <= old)) (PreH21 : (old <= count)) (PreH22 : (count <= x_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= old)) (PreH25 : (count = (Zlength (products_before_append)))) (PreH26 : (reaches = 1)) (PreH27 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH28 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH29 : (ValuableOuterState x_pre values i segments base_products_2 )) (PreH30 : (ValuableForcedHistory x_pre values i segments base_products_2 )) (PreH31 : (ValuableAlignedHistory x_pre values i segments base_products_2 )) (PreH32 : (ValuableClosureState x_pre segment_2 v base_products_2 j products_before_append reaches )) (PreH33 : (ValuableBitmap x_pre products_before_append bitmap_2 )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap_2 )
|--
  EX (segment: (@list Z)) (bitmap: (@list Z)) (products: (@list Z)) (base_products: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products))) ”
  &&  “ (1 <= old) ”
  &&  “ (old <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= old) ”
  &&  “ (count = (Zlength (products))) ”
  &&  “ (reaches = 1) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products (j + 1 ) products reaches ) ”
  &&  “ (ValuableBitmap x_pre products bitmap ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment_2: (@list Z)) (bitmap_2: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products_2: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((Znth (j - 0 ) products_before_append 0) > (x_pre ÷ v ))) (PreH2 : (j < old)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 100000)) (PreH6 : (1 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH9 : (Pre x_pre values )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (v = (Znth i values 0))) (PreH13 : (1 <= v)) (PreH14 : (v <= x_pre)) (PreH15 : ((x_pre % ( v ) ) = 0)) (PreH16 : (1 <= segments)) (PreH17 : (segments <= (i + 1 ))) (PreH18 : (old = (Zlength (base_products_2)))) (PreH19 : (base_products_2 = (sublist (0) (old) (products_before_append)))) (PreH20 : (1 <= old)) (PreH21 : (old <= count)) (PreH22 : (count <= x_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= old)) (PreH25 : (count = (Zlength (products_before_append)))) (PreH26 : (reaches = 1)) (PreH27 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH28 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH29 : (ValuableOuterState x_pre values i segments base_products_2 )) (PreH30 : (ValuableForcedHistory x_pre values i segments base_products_2 )) (PreH31 : (ValuableAlignedHistory x_pre values i segments base_products_2 )) (PreH32 : (ValuableClosureState x_pre segment_2 v base_products_2 j products_before_append reaches )) (PreH33 : (ValuableBitmap x_pre products_before_append bitmap_2 )),
  TT && emp 
|--
  EX (segment: (@list Z)),
  “ ((Zlength ((sublist (0) (old) (products_before_append)))) = (Zlength ((sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append))))) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (Zlength ((sublist (0) (old) (products_before_append))))) ”
  &&  “ (ValuableOuterState x_pre values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append)) ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append)) ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append)) ) ”
  &&  “ (ValuableClosureState x_pre segment (Znth i values 0) (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append)) (j + 1 ) products_before_append 1 ) ”
  &&  emp
).

Definition solver_entail_wit_6_11 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment_2: (@list Z)) (bitmap_2: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products_2: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) <> 0)) (PreH2 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH3 : (j < old)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 100000)) (PreH7 : (1 <= (Zlength (values)))) (PreH8 : ((Zlength (values)) <= 100000)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH10 : (Pre x_pre values )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (v = (Znth i values 0))) (PreH14 : (1 <= v)) (PreH15 : (v <= x_pre)) (PreH16 : ((x_pre % ( v ) ) = 0)) (PreH17 : (1 <= segments)) (PreH18 : (segments <= (i + 1 ))) (PreH19 : (old = (Zlength (base_products_2)))) (PreH20 : (base_products_2 = (sublist (0) (old) (products_before_append)))) (PreH21 : (1 <= old)) (PreH22 : (old <= count)) (PreH23 : (count <= x_pre)) (PreH24 : (0 <= j)) (PreH25 : (j <= old)) (PreH26 : (count = (Zlength (products_before_append)))) (PreH27 : (reaches = 1)) (PreH28 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH29 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH30 : (ValuableOuterState x_pre values i segments base_products_2 )) (PreH31 : (ValuableForcedHistory x_pre values i segments base_products_2 )) (PreH32 : (ValuableAlignedHistory x_pre values i segments base_products_2 )) (PreH33 : (ValuableClosureState x_pre segment_2 v base_products_2 j products_before_append reaches )) (PreH34 : (ValuableBitmap x_pre products_before_append bitmap_2 )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap_2 )
|--
  EX (segment: (@list Z)) (bitmap: (@list Z)) (products: (@list Z)) (base_products: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products))) ”
  &&  “ (1 <= old) ”
  &&  “ (old <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= old) ”
  &&  “ (count = (Zlength (products))) ”
  &&  “ (reaches = 1) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products (j + 1 ) products reaches ) ”
  &&  “ (ValuableBitmap x_pre products bitmap ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment_2: (@list Z)) (bitmap_2: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products_2: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) <> 0)) (PreH2 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH3 : (j < old)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 100000)) (PreH7 : (1 <= (Zlength (values)))) (PreH8 : ((Zlength (values)) <= 100000)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH10 : (Pre x_pre values )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (v = (Znth i values 0))) (PreH14 : (1 <= v)) (PreH15 : (v <= x_pre)) (PreH16 : ((x_pre % ( v ) ) = 0)) (PreH17 : (1 <= segments)) (PreH18 : (segments <= (i + 1 ))) (PreH19 : (old = (Zlength (base_products_2)))) (PreH20 : (base_products_2 = (sublist (0) (old) (products_before_append)))) (PreH21 : (1 <= old)) (PreH22 : (old <= count)) (PreH23 : (count <= x_pre)) (PreH24 : (0 <= j)) (PreH25 : (j <= old)) (PreH26 : (count = (Zlength (products_before_append)))) (PreH27 : (reaches = 1)) (PreH28 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH29 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH30 : (ValuableOuterState x_pre values i segments base_products_2 )) (PreH31 : (ValuableForcedHistory x_pre values i segments base_products_2 )) (PreH32 : (ValuableAlignedHistory x_pre values i segments base_products_2 )) (PreH33 : (ValuableClosureState x_pre segment_2 v base_products_2 j products_before_append reaches )) (PreH34 : (ValuableBitmap x_pre products_before_append bitmap_2 )),
  TT && emp 
|--
  EX (segment: (@list Z)),
  “ ((Zlength ((sublist (0) (old) (products_before_append)))) = (Zlength ((sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append))))) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (Zlength ((sublist (0) (old) (products_before_append))))) ”
  &&  “ (ValuableOuterState x_pre values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append)) ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append)) ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append)) ) ”
  &&  “ (ValuableClosureState x_pre segment (Znth i values 0) (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append)) (j + 1 ) products_before_append 1 ) ”
  &&  emp
).

Definition solver_entail_wit_6_12 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment_2: (@list Z)) (bitmap_2: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products_2: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) <> 0)) (PreH2 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH3 : (j < old)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 100000)) (PreH7 : (1 <= (Zlength (values)))) (PreH8 : ((Zlength (values)) <= 100000)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH10 : (Pre x_pre values )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (v = (Znth i values 0))) (PreH14 : (1 <= v)) (PreH15 : (v <= x_pre)) (PreH16 : ((x_pre % ( v ) ) = 0)) (PreH17 : (1 <= segments)) (PreH18 : (segments <= (i + 1 ))) (PreH19 : (old = (Zlength (base_products_2)))) (PreH20 : (base_products_2 = (sublist (0) (old) (products_before_append)))) (PreH21 : (1 <= old)) (PreH22 : (old <= count)) (PreH23 : (count <= x_pre)) (PreH24 : (0 <= j)) (PreH25 : (j <= old)) (PreH26 : (count = (Zlength (products_before_append)))) (PreH27 : (reaches = 0)) (PreH28 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH29 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH30 : (ValuableOuterState x_pre values i segments base_products_2 )) (PreH31 : (ValuableForcedHistory x_pre values i segments base_products_2 )) (PreH32 : (ValuableAlignedHistory x_pre values i segments base_products_2 )) (PreH33 : (ValuableClosureState x_pre segment_2 v base_products_2 j products_before_append reaches )) (PreH34 : (ValuableBitmap x_pre products_before_append bitmap_2 )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap_2 )
|--
  EX (segment: (@list Z)) (bitmap: (@list Z)) (products: (@list Z)) (base_products: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products))) ”
  &&  “ (1 <= old) ”
  &&  “ (old <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= old) ”
  &&  “ (count = (Zlength (products))) ”
  &&  “ (reaches = 0) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products (j + 1 ) products reaches ) ”
  &&  “ (ValuableBitmap x_pre products bitmap ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment_2: (@list Z)) (bitmap_2: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products_2: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) <> 0)) (PreH2 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH3 : (j < old)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 100000)) (PreH7 : (1 <= (Zlength (values)))) (PreH8 : ((Zlength (values)) <= 100000)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH10 : (Pre x_pre values )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (v = (Znth i values 0))) (PreH14 : (1 <= v)) (PreH15 : (v <= x_pre)) (PreH16 : ((x_pre % ( v ) ) = 0)) (PreH17 : (1 <= segments)) (PreH18 : (segments <= (i + 1 ))) (PreH19 : (old = (Zlength (base_products_2)))) (PreH20 : (base_products_2 = (sublist (0) (old) (products_before_append)))) (PreH21 : (1 <= old)) (PreH22 : (old <= count)) (PreH23 : (count <= x_pre)) (PreH24 : (0 <= j)) (PreH25 : (j <= old)) (PreH26 : (count = (Zlength (products_before_append)))) (PreH27 : (reaches = 0)) (PreH28 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH29 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH30 : (ValuableOuterState x_pre values i segments base_products_2 )) (PreH31 : (ValuableForcedHistory x_pre values i segments base_products_2 )) (PreH32 : (ValuableAlignedHistory x_pre values i segments base_products_2 )) (PreH33 : (ValuableClosureState x_pre segment_2 v base_products_2 j products_before_append reaches )) (PreH34 : (ValuableBitmap x_pre products_before_append bitmap_2 )),
  TT && emp 
|--
  EX (segment: (@list Z)),
  “ ((Zlength ((sublist (0) (old) (products_before_append)))) = (Zlength ((sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append))))) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (Zlength ((sublist (0) (old) (products_before_append))))) ”
  &&  “ (ValuableOuterState x_pre values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append)) ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append)) ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append)) ) ”
  &&  “ (ValuableClosureState x_pre segment (Znth i values 0) (sublist (0) ((Zlength ((sublist (0) (old) (products_before_append))))) (products_before_append)) (j + 1 ) products_before_append 0 ) ”
  &&  emp
).

Definition solver_entail_wit_7_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (products: (@list Z)) (bitmap: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (products_buf: Z) (used: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH7 : (Pre x_pre values )) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (v = (Znth i values 0))) (PreH11 : (1 <= v)) (PreH12 : (v <= x_pre)) (PreH13 : ((x_pre % ( v ) ) = 0)) (PreH14 : (1 <= segments)) (PreH15 : (segments <= (i + 1 ))) (PreH16 : (old = (Zlength (base_products)))) (PreH17 : (base_products = (sublist (0) (old) (products)))) (PreH18 : (1 <= old)) (PreH19 : (old <= count)) (PreH20 : (count <= x_pre)) (PreH21 : (count = (Zlength (products)))) (PreH22 : (reaches = 1)) (PreH23 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH24 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre)))) (PreH25 : (ValuableOuterState x_pre values i segments base_products )) (PreH26 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH27 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH28 : (ValuableClosureState x_pre segment v base_products old products reaches )) (PreH29 : (ValuableBitmap x_pre products bitmap )) (PreH30 : (reaches = 0)),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products))) ”
  &&  “ (1 <= old) ”
  &&  “ (old <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (count = (Zlength (products))) ”
  &&  “ (reaches = 0) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products old products reaches ) ”
  &&  “ (ValuableBitmap x_pre products bitmap ) ”
  &&  “ (reaches = 0) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
.

Definition solver_entail_wit_7_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (products: (@list Z)) (bitmap: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (products_buf: Z) (used: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH7 : (Pre x_pre values )) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (v = (Znth i values 0))) (PreH11 : (1 <= v)) (PreH12 : (v <= x_pre)) (PreH13 : ((x_pre % ( v ) ) = 0)) (PreH14 : (1 <= segments)) (PreH15 : (segments <= (i + 1 ))) (PreH16 : (old = (Zlength (base_products)))) (PreH17 : (base_products = (sublist (0) (old) (products)))) (PreH18 : (1 <= old)) (PreH19 : (old <= count)) (PreH20 : (count <= x_pre)) (PreH21 : (count = (Zlength (products)))) (PreH22 : (reaches = 0)) (PreH23 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH24 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre)))) (PreH25 : (ValuableOuterState x_pre values i segments base_products )) (PreH26 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH27 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH28 : (ValuableClosureState x_pre segment v base_products old products reaches )) (PreH29 : (ValuableBitmap x_pre products bitmap )) (PreH30 : (reaches = 0)),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products))) ”
  &&  “ (1 <= old) ”
  &&  “ (old <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (count = (Zlength (products))) ”
  &&  “ (reaches = 0) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products old products reaches ) ”
  &&  “ (ValuableBitmap x_pre products bitmap ) ”
  &&  “ (reaches = 0) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
.

Definition solver_entail_wit_8_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (products: (@list Z)) (bitmap: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (products_buf: Z) (used: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH7 : (Pre x_pre values )) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (v = (Znth i values 0))) (PreH11 : (1 <= v)) (PreH12 : (v <= x_pre)) (PreH13 : ((x_pre % ( v ) ) = 0)) (PreH14 : (1 <= segments)) (PreH15 : (segments <= (i + 1 ))) (PreH16 : (old = (Zlength (base_products)))) (PreH17 : (base_products = (sublist (0) (old) (products)))) (PreH18 : (1 <= old)) (PreH19 : (old <= count)) (PreH20 : (count <= x_pre)) (PreH21 : (count = (Zlength (products)))) (PreH22 : (reaches = 1)) (PreH23 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH24 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre)))) (PreH25 : (ValuableOuterState x_pre values i segments base_products )) (PreH26 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH27 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH28 : (ValuableClosureState x_pre segment v base_products old products reaches )) (PreH29 : (ValuableBitmap x_pre products bitmap )) (PreH30 : (reaches <> 0)),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products))) ”
  &&  “ (1 <= old) ”
  &&  “ (old <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (count = (Zlength (products))) ”
  &&  “ (reaches = 1) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products old products reaches ) ”
  &&  “ (ValuableBitmap x_pre products bitmap ) ”
  &&  “ (reaches <> 0) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
.

Definition solver_entail_wit_8_2 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (products: (@list Z)) (bitmap: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (products_buf: Z) (used: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH7 : (Pre x_pre values )) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (v = (Znth i values 0))) (PreH11 : (1 <= v)) (PreH12 : (v <= x_pre)) (PreH13 : ((x_pre % ( v ) ) = 0)) (PreH14 : (1 <= segments)) (PreH15 : (segments <= (i + 1 ))) (PreH16 : (old = (Zlength (base_products)))) (PreH17 : (base_products = (sublist (0) (old) (products)))) (PreH18 : (1 <= old)) (PreH19 : (old <= count)) (PreH20 : (count <= x_pre)) (PreH21 : (count = (Zlength (products)))) (PreH22 : (reaches = 0)) (PreH23 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH24 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre)))) (PreH25 : (ValuableOuterState x_pre values i segments base_products )) (PreH26 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH27 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH28 : (ValuableClosureState x_pre segment v base_products old products reaches )) (PreH29 : (ValuableBitmap x_pre products bitmap )) (PreH30 : (reaches <> 0)),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products))) ”
  &&  “ (1 <= old) ”
  &&  “ (old <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (count = (Zlength (products))) ”
  &&  “ (reaches = 1) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products old products reaches ) ”
  &&  “ (ValuableBitmap x_pre products bitmap ) ”
  &&  “ (reaches <> 0) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
.

Definition solver_entail_wit_9 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (segment_2: (@list Z)) (base_products_2: (@list Z)) (products_2: (@list Z)) (bitmap_2: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (products_buf: Z) (used: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 200000)))) (PreH7 : (Pre x_pre values )) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (v = (Znth i values 0))) (PreH11 : (1 <= v)) (PreH12 : (v <= x_pre)) (PreH13 : ((x_pre % ( v ) ) = 0)) (PreH14 : (1 <= segments)) (PreH15 : (segments <= (i + 1 ))) (PreH16 : (old = (Zlength (base_products_2)))) (PreH17 : (base_products_2 = (sublist (0) (old) (products_2)))) (PreH18 : (1 <= old)) (PreH19 : (old <= count)) (PreH20 : (count <= x_pre)) (PreH21 : (count = (Zlength (products_2)))) (PreH22 : (reaches = 1)) (PreH23 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH24 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < count)) -> ((1 <= (Znth k_4 products_2 0)) /\ ((Znth k_4 products_2 0) <= x_pre)))) (PreH25 : (ValuableOuterState x_pre values i segments base_products_2 )) (PreH26 : (ValuableForcedHistory x_pre values i segments base_products_2 )) (PreH27 : (ValuableAlignedHistory x_pre values i segments base_products_2 )) (PreH28 : (ValuableClosureState x_pre segment_2 v base_products_2 old products_2 reaches )) (PreH29 : (ValuableBitmap x_pre products_2 bitmap_2 )) (PreH30 : (reaches <> 0)),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products_2 )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap_2 )
|--
  EX (segment: (@list Z)) (bitmap: (@list Z)) (products: (@list Z)) (base_products: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (2 <= (segments + 1 )) ”
  &&  “ ((segments + 1 ) <= (i + 2 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products))) ”
  &&  “ (count = (Zlength (products))) ”
  &&  “ (1 <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= count) ”
  &&  “ (reaches = 1) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i ((segments + 1 ) - 1 ) base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i ((segments + 1 ) - 1 ) base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i ((segments + 1 ) - 1 ) base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products old products 1 ) ”
  &&  “ (ValuableClearingState x_pre products 0 bitmap ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment_2: (@list Z)) (base_products_2: (@list Z)) (products_2: (@list Z)) (bitmap_2: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 200000)))) (PreH7 : (Pre x_pre values )) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (v = (Znth i values 0))) (PreH11 : (1 <= v)) (PreH12 : (v <= x_pre)) (PreH13 : ((x_pre % ( v ) ) = 0)) (PreH14 : (1 <= segments)) (PreH15 : (segments <= (i + 1 ))) (PreH16 : (old = (Zlength (base_products_2)))) (PreH17 : (base_products_2 = (sublist (0) (old) (products_2)))) (PreH18 : (1 <= old)) (PreH19 : (old <= count)) (PreH20 : (count <= x_pre)) (PreH21 : (count = (Zlength (products_2)))) (PreH22 : (reaches = 1)) (PreH23 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH24 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < count)) -> ((1 <= (Znth k_4 products_2 0)) /\ ((Znth k_4 products_2 0) <= x_pre)))) (PreH25 : (ValuableOuterState x_pre values i segments base_products_2 )) (PreH26 : (ValuableForcedHistory x_pre values i segments base_products_2 )) (PreH27 : (ValuableAlignedHistory x_pre values i segments base_products_2 )) (PreH28 : (ValuableClosureState x_pre segment_2 v base_products_2 old products_2 reaches )) (PreH29 : (ValuableBitmap x_pre products_2 bitmap_2 )) (PreH30 : (reaches <> 0)),
  TT && emp 
|--
  EX (segment: (@list Z)),
  “ (2 <= (segments + 1 )) ”
  &&  “ ((segments + 1 ) <= (i + 2 )) ”
  &&  “ ((Zlength ((sublist (0) (old) (products_2)))) = (Zlength ((sublist (0) ((Zlength ((sublist (0) (old) (products_2))))) (products_2))))) ”
  &&  “ (1 <= (Zlength (products_2))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (Zlength (products_2))) ”
  &&  “ (ValuableOuterState x_pre values i ((segments + 1 ) - 1 ) (sublist (0) ((Zlength ((sublist (0) (old) (products_2))))) (products_2)) ) ”
  &&  “ (ValuableForcedHistory x_pre values i ((segments + 1 ) - 1 ) (sublist (0) ((Zlength ((sublist (0) (old) (products_2))))) (products_2)) ) ”
  &&  “ (ValuableAlignedHistory x_pre values i ((segments + 1 ) - 1 ) (sublist (0) ((Zlength ((sublist (0) (old) (products_2))))) (products_2)) ) ”
  &&  “ (ValuableClosureState x_pre segment (Znth i values 0) (sublist (0) ((Zlength ((sublist (0) (old) (products_2))))) (products_2)) (Zlength ((sublist (0) (old) (products_2)))) products_2 1 ) ”
  &&  “ (ValuableClearingState x_pre products_2 0 bitmap_2 ) ”
  &&  emp
).

Definition solver_entail_wit_10 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment_2: (@list Z)) (bitmap_2: (@list Z)) (reaches: Z) (j: Z) (count: Z) (products_2: (@list Z)) (base_products_2: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (PreH1 : (j < count)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (v = (Znth i values 0))) (PreH12 : (1 <= v)) (PreH13 : (v <= x_pre)) (PreH14 : ((x_pre % ( v ) ) = 0)) (PreH15 : (2 <= segments)) (PreH16 : (segments <= (i + 2 ))) (PreH17 : (old = (Zlength (base_products_2)))) (PreH18 : (base_products_2 = (sublist (0) (old) (products_2)))) (PreH19 : (count = (Zlength (products_2)))) (PreH20 : (1 <= count)) (PreH21 : (count <= x_pre)) (PreH22 : (0 <= j)) (PreH23 : (j <= count)) (PreH24 : (reaches = 1)) (PreH25 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH26 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_2 0)) /\ ((Znth k_2 products_2 0) <= x_pre)))) (PreH27 : (ValuableOuterState x_pre values i (segments - 1 ) base_products_2 )) (PreH28 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products_2 )) (PreH29 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products_2 )) (PreH30 : (ValuableClosureState x_pre segment_2 v base_products_2 old products_2 1 )) (PreH31 : (ValuableClearingState x_pre products_2 j bitmap_2 )),
  (UCharArray.full used (x_pre + 1 ) (replace_Znth ((Znth (j - 0 ) products_2 0)) (0) (bitmap_2)) )
  **  (IntArray.seg products_buf 0 count products_2 )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
|--
  EX (segment: (@list Z)) (bitmap: (@list Z)) (products: (@list Z)) (base_products: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (2 <= segments) ”
  &&  “ (segments <= (i + 2 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products))) ”
  &&  “ (count = (Zlength (products))) ”
  &&  “ (1 <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= count) ”
  &&  “ (reaches = 1) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i (segments - 1 ) base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i (segments - 1 ) base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products old products 1 ) ”
  &&  “ (ValuableClearingState x_pre products (j + 1 ) bitmap ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment_2: (@list Z)) (bitmap_2: (@list Z)) (reaches: Z) (j: Z) (count: Z) (products_2: (@list Z)) (base_products_2: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (PreH1 : (j < count)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (v = (Znth i values 0))) (PreH12 : (1 <= v)) (PreH13 : (v <= x_pre)) (PreH14 : ((x_pre % ( v ) ) = 0)) (PreH15 : (2 <= segments)) (PreH16 : (segments <= (i + 2 ))) (PreH17 : (old = (Zlength (base_products_2)))) (PreH18 : (base_products_2 = (sublist (0) (old) (products_2)))) (PreH19 : (count = (Zlength (products_2)))) (PreH20 : (1 <= count)) (PreH21 : (count <= x_pre)) (PreH22 : (0 <= j)) (PreH23 : (j <= count)) (PreH24 : (reaches = 1)) (PreH25 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH26 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_2 0)) /\ ((Znth k_2 products_2 0) <= x_pre)))) (PreH27 : (ValuableOuterState x_pre values i (segments - 1 ) base_products_2 )) (PreH28 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products_2 )) (PreH29 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products_2 )) (PreH30 : (ValuableClosureState x_pre segment_2 v base_products_2 old products_2 1 )) (PreH31 : (ValuableClearingState x_pre products_2 j bitmap_2 )),
  TT && emp 
|--
  EX (segment: (@list Z)),
  “ ((Zlength ((sublist (0) (old) (products_2)))) = (Zlength ((sublist (0) ((Zlength ((sublist (0) (old) (products_2))))) (products_2))))) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (Zlength (products_2))) ”
  &&  “ ((Zlength ((replace_Znth ((Znth (j - 0 ) products_2 0)) (0) (bitmap_2)))) = (x_pre + 1 )) ”
  &&  “ (ValuableOuterState x_pre values i (segments - 1 ) (sublist (0) ((Zlength ((sublist (0) (old) (products_2))))) (products_2)) ) ”
  &&  “ (ValuableForcedHistory x_pre values i (segments - 1 ) (sublist (0) ((Zlength ((sublist (0) (old) (products_2))))) (products_2)) ) ”
  &&  “ (ValuableAlignedHistory x_pre values i (segments - 1 ) (sublist (0) ((Zlength ((sublist (0) (old) (products_2))))) (products_2)) ) ”
  &&  “ (ValuableClosureState x_pre segment (Znth i values 0) (sublist (0) ((Zlength ((sublist (0) (old) (products_2))))) (products_2)) (Zlength ((sublist (0) (old) (products_2)))) products_2 1 ) ”
  &&  “ (ValuableClearingState x_pre products_2 (j + 1 ) (replace_Znth ((Znth (j - 0 ) products_2 0)) (0) (bitmap_2)) ) ”
  &&  emp
).

Definition solver_entail_wit_11 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment_2: (@list Z)) (bitmap_2: (@list Z)) (reaches: Z) (j: Z) (count: Z) (products: (@list Z)) (base_products_2: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (PreH1 : (j >= count)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (v = (Znth i values 0))) (PreH12 : (1 <= v)) (PreH13 : (v <= x_pre)) (PreH14 : ((x_pre % ( v ) ) = 0)) (PreH15 : (2 <= segments)) (PreH16 : (segments <= (i + 2 ))) (PreH17 : (old = (Zlength (base_products_2)))) (PreH18 : (base_products_2 = (sublist (0) (old) (products)))) (PreH19 : (count = (Zlength (products)))) (PreH20 : (1 <= count)) (PreH21 : (count <= x_pre)) (PreH22 : (0 <= j)) (PreH23 : (j <= count)) (PreH24 : (reaches = 1)) (PreH25 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH26 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < count)) -> ((1 <= (Znth k_3 products 0)) /\ ((Znth k_3 products 0) <= x_pre)))) (PreH27 : (ValuableOuterState x_pre values i (segments - 1 ) base_products_2 )) (PreH28 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products_2 )) (PreH29 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products_2 )) (PreH30 : (ValuableClosureState x_pre segment_2 v base_products_2 old products 1 )) (PreH31 : (ValuableClearingState x_pre products j bitmap_2 )),
  (UCharArray.full used (x_pre + 1 ) (replace_Znth (1) (1) (bitmap_2)) )
  **  (IntArray.full products_buf count (replace_Znth (0) (1) (products)) )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
|--
  EX (bitmap: (@list Z)) (segment: (@list Z)) (old_products: (@list Z)) (base_products: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (2 <= segments) ”
  &&  “ (segments <= (i + 2 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (old_products))) ”
  &&  “ (1 = 1) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= x_pre) ”
  &&  “ (reaches = 1) ”
  &&  “ (ValuableOuterState x_pre values i (segments - 1 ) base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i (segments - 1 ) base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products old old_products 1 ) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ (ValuableBitmap x_pre (cons (1) ((@nil Z))) bitmap ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 1 (cons (1) ((@nil Z))) )
  **  (IntArray.undef_seg products_buf 1 (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (products_buf: Z) (segment_2: (@list Z)) (bitmap_2: (@list Z)) (reaches: Z) (j: Z) (count: Z) (products: (@list Z)) (base_products_2: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (PreH1 : (j >= count)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (values)))) -> ((1 <= (Znth k_2 values 0)) /\ ((Znth k_2 values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (v = (Znth i values 0))) (PreH12 : (1 <= v)) (PreH13 : (v <= x_pre)) (PreH14 : ((x_pre % ( v ) ) = 0)) (PreH15 : (2 <= segments)) (PreH16 : (segments <= (i + 2 ))) (PreH17 : (old = (Zlength (base_products_2)))) (PreH18 : (base_products_2 = (sublist (0) (old) (products)))) (PreH19 : (count = (Zlength (products)))) (PreH20 : (1 <= count)) (PreH21 : (count <= x_pre)) (PreH22 : (0 <= j)) (PreH23 : (j <= count)) (PreH24 : (reaches = 1)) (PreH25 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH26 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < count)) -> ((1 <= (Znth k_3 products 0)) /\ ((Znth k_3 products 0) <= x_pre)))) (PreH27 : (ValuableOuterState x_pre values i (segments - 1 ) base_products_2 )) (PreH28 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products_2 )) (PreH29 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products_2 )) (PreH30 : (ValuableClosureState x_pre segment_2 v base_products_2 old products 1 )) (PreH31 : (ValuableClearingState x_pre products j bitmap_2 )),
  (IntArray.full products_buf count (replace_Znth (0) (1) (products)) )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
|--
  EX (segment: (@list Z)) (old_products: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (2 <= segments) ”
  &&  “ (segments <= (i + 2 )) ”
  &&  “ (old = (Zlength ((sublist (0) (old) (old_products))))) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= x_pre) ”
  &&  “ (reaches = 1) ”
  &&  “ (ValuableOuterState x_pre values i (segments - 1 ) (sublist (0) (old) (old_products)) ) ”
  &&  “ (ValuableForcedHistory x_pre values i (segments - 1 ) (sublist (0) (old) (old_products)) ) ”
  &&  “ (ValuableAlignedHistory x_pre values i (segments - 1 ) (sublist (0) (old) (old_products)) ) ”
  &&  “ (ValuableClosureState x_pre segment v (sublist (0) (old) (old_products)) old old_products 1 ) ”
  &&  “ ((Zlength ((replace_Znth (1) (1) (bitmap_2)))) = (x_pre + 1 )) ”
  &&  “ (ValuableBitmap x_pre (cons (1) ((@nil Z))) (replace_Znth (1) (1) (bitmap_2)) ) ”
  &&  (IntArray.seg products_buf 0 1 (cons (1) ((@nil Z))) )
  **  (IntArray.undef_seg products_buf 1 (x_pre + 1 ) )
).

Definition solver_entail_wit_12 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (old_products: (@list Z)) (bitmap: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (products_buf: Z) (used: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH7 : (Pre x_pre values )) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (v = (Znth i values 0))) (PreH11 : (1 <= v)) (PreH12 : (v <= x_pre)) (PreH13 : ((x_pre % ( v ) ) = 0)) (PreH14 : (2 <= segments)) (PreH15 : (segments <= (i + 2 ))) (PreH16 : (old = (Zlength (base_products)))) (PreH17 : (base_products = (sublist (0) (old) (old_products)))) (PreH18 : (count = 1)) (PreH19 : (1 <= count)) (PreH20 : (count <= x_pre)) (PreH21 : (reaches = 1)) (PreH22 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH23 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH24 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH25 : (ValuableClosureState x_pre segment v base_products old old_products 1 )) (PreH26 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH27 : (ValuableBitmap x_pre (cons (1) ((@nil Z))) bitmap )),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.seg products_buf 0 count (cons (1) ((@nil Z))) )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (0 <= v) ”
  &&  “ (v < (x_pre + 1 )) ”
  &&  “ (reaches <= INT_MAX) ”
  &&  “ (count <= INT_MAX) ”
  &&  “ (old <= INT_MAX) ”
  &&  “ (segments <= INT_MAX) ”
  &&  “ (i <= INT_MAX) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (reaches >= INT_MIN) ”
  &&  “ (count >= INT_MIN) ”
  &&  “ (old >= INT_MIN) ”
  &&  “ (segments >= INT_MIN) ”
  &&  “ (i >= INT_MIN) ”
  &&  “ (n_pre >= INT_MIN) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (2 <= segments) ”
  &&  “ (segments <= (i + 2 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (old_products))) ”
  &&  “ (count = 1) ”
  &&  “ (1 <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (reaches = 1) ”
  &&  “ (ValuableOuterState x_pre values i (segments - 1 ) base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i (segments - 1 ) base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products old old_products 1 ) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ (ValuableBitmap x_pre (cons (1) ((@nil Z))) bitmap ) ”
  &&  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "old" ) )) # Int  |-> old)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "reaches" ) )) # Int  |-> reaches)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.seg products_buf 0 count (cons (1) ((@nil Z))) )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
.

Definition solver_entail_wit_13 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (old_products: (@list Z)) (bitmap: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (products_buf: Z) (used: Z) (PreH1 : ((Znth v bitmap 0) = 0)) (PreH2 : (0 <= v)) (PreH3 : (v < (x_pre + 1 ))) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (count <= INT_MAX)) (PreH6 : (old <= INT_MAX)) (PreH7 : (segments <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (reaches >= INT_MIN)) (PreH11 : (count >= INT_MIN)) (PreH12 : (old >= INT_MIN)) (PreH13 : (segments >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (2 <= x_pre)) (PreH18 : (x_pre <= 100000)) (PreH19 : (1 <= (Zlength (values)))) (PreH20 : ((Zlength (values)) <= 100000)) (PreH21 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH22 : (Pre x_pre values )) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (v = (Znth i values 0))) (PreH26 : (1 <= v)) (PreH27 : (v <= x_pre)) (PreH28 : ((x_pre % ( v ) ) = 0)) (PreH29 : (2 <= segments)) (PreH30 : (segments <= (i + 2 ))) (PreH31 : (old = (Zlength (base_products)))) (PreH32 : (base_products = (sublist (0) (old) (old_products)))) (PreH33 : (count = 1)) (PreH34 : (1 <= count)) (PreH35 : (count <= x_pre)) (PreH36 : (reaches = 1)) (PreH37 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH38 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH39 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH40 : (ValuableClosureState x_pre segment v base_products old old_products 1 )) (PreH41 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH42 : (ValuableBitmap x_pre (cons (1) ((@nil Z))) bitmap )),
  (IntArray.seg products_buf 0 (count + 1 ) (app ((cons (1) ((@nil Z)))) ((cons (v) ((@nil Z))))) )
  **  (IntArray.undef_seg products_buf (count + 1 ) (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) (replace_Znth (v) (1) (bitmap)) )
  **  (IntArray.full a_pre n_pre values )
|--
  “ ((Znth v bitmap 0) = 0) ”
  &&  “ (0 <= v) ”
  &&  “ (v < (x_pre + 1 )) ”
  &&  “ (reaches <= INT_MAX) ”
  &&  “ (count <= INT_MAX) ”
  &&  “ (old <= INT_MAX) ”
  &&  “ (segments <= INT_MAX) ”
  &&  “ (i <= INT_MAX) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (reaches >= INT_MIN) ”
  &&  “ (count >= INT_MIN) ”
  &&  “ (old >= INT_MIN) ”
  &&  “ (segments >= INT_MIN) ”
  &&  “ (i >= INT_MIN) ”
  &&  “ (n_pre >= INT_MIN) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (2 <= segments) ”
  &&  “ (segments <= (i + 2 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (old_products))) ”
  &&  “ (count = 1) ”
  &&  “ (1 <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (reaches = 1) ”
  &&  “ (ValuableOuterState x_pre values i (segments - 1 ) base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i (segments - 1 ) base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products old old_products 1 ) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ (ValuableBitmap x_pre (cons (1) ((@nil Z))) bitmap ) ”
  &&  (IntArray.seg products_buf 0 (count + 1 ) (cons (1) ((cons (v) ((@nil Z))))) )
  **  (IntArray.undef_seg products_buf (count + 1 ) (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) (replace_Znth (v) (1) (bitmap)) )
  **  (IntArray.full a_pre n_pre values )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (old_products: (@list Z)) (bitmap: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (PreH1 : ((Znth v bitmap 0) = 0)) (PreH2 : (0 <= v)) (PreH3 : (v < (x_pre + 1 ))) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (count <= INT_MAX)) (PreH6 : (old <= INT_MAX)) (PreH7 : (segments <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (reaches >= INT_MIN)) (PreH11 : (count >= INT_MIN)) (PreH12 : (old >= INT_MIN)) (PreH13 : (segments >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (2 <= x_pre)) (PreH18 : (x_pre <= 100000)) (PreH19 : (1 <= (Zlength (values)))) (PreH20 : ((Zlength (values)) <= 100000)) (PreH21 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH22 : (Pre x_pre values )) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (v = (Znth i values 0))) (PreH26 : (1 <= v)) (PreH27 : (v <= x_pre)) (PreH28 : ((x_pre % ( v ) ) = 0)) (PreH29 : (2 <= segments)) (PreH30 : (segments <= (i + 2 ))) (PreH31 : (old = (Zlength (base_products)))) (PreH32 : (base_products = (sublist (0) (old) (old_products)))) (PreH33 : (count = 1)) (PreH34 : (1 <= count)) (PreH35 : (count <= x_pre)) (PreH36 : (reaches = 1)) (PreH37 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH38 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH39 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH40 : (ValuableClosureState x_pre segment v base_products old old_products 1 )) (PreH41 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH42 : (ValuableBitmap x_pre (cons (1) ((@nil Z))) bitmap )),
  TT && emp 
|--
  “ ((app ((cons (1) ((@nil Z)))) ((cons (v) ((@nil Z))))) = (cons (1) ((cons (v) ((@nil Z)))))) ”
  &&  emp
).

Definition solver_entail_wit_13_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (old_products: (@list Z)) (bitmap: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (PreH1 : ((Znth v bitmap 0) = 0)) (PreH2 : (0 <= v)) (PreH3 : (v < (x_pre + 1 ))) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (count <= INT_MAX)) (PreH6 : (old <= INT_MAX)) (PreH7 : (segments <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (reaches >= INT_MIN)) (PreH11 : (count >= INT_MIN)) (PreH12 : (old >= INT_MIN)) (PreH13 : (segments >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (2 <= x_pre)) (PreH18 : (x_pre <= 100000)) (PreH19 : (1 <= (Zlength (values)))) (PreH20 : ((Zlength (values)) <= 100000)) (PreH21 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH22 : (Pre x_pre values )) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (v = (Znth i values 0))) (PreH26 : (1 <= v)) (PreH27 : (v <= x_pre)) (PreH28 : ((x_pre % ( v ) ) = 0)) (PreH29 : (2 <= segments)) (PreH30 : (segments <= (i + 2 ))) (PreH31 : (old = (Zlength (base_products)))) (PreH32 : (base_products = (sublist (0) (old) (old_products)))) (PreH33 : (count = 1)) (PreH34 : (1 <= count)) (PreH35 : (count <= x_pre)) (PreH36 : (reaches = 1)) (PreH37 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH38 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH39 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH40 : (ValuableClosureState x_pre segment v base_products old old_products 1 )) (PreH41 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH42 : (ValuableBitmap x_pre (cons (1) ((@nil Z))) bitmap )),
  ((app ((cons (1) ((@nil Z)))) ((cons (v) ((@nil Z))))) = (cons (1) ((cons (v) ((@nil Z))))))
.

Definition solver_entail_wit_14_1 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (old_products: (@list Z)) (bitmap_2: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (products_buf: Z) (used: Z) (PreH1 : ((Znth v bitmap_2 0) = 0)) (PreH2 : (0 <= v)) (PreH3 : (v < (x_pre + 1 ))) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (count <= INT_MAX)) (PreH6 : (old <= INT_MAX)) (PreH7 : (segments <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (reaches >= INT_MIN)) (PreH11 : (count >= INT_MIN)) (PreH12 : (old >= INT_MIN)) (PreH13 : (segments >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (2 <= x_pre)) (PreH18 : (x_pre <= 100000)) (PreH19 : (1 <= (Zlength (values)))) (PreH20 : ((Zlength (values)) <= 100000)) (PreH21 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 200000)))) (PreH22 : (Pre x_pre values )) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (v = (Znth i values 0))) (PreH26 : (1 <= v)) (PreH27 : (v <= x_pre)) (PreH28 : ((x_pre % ( v ) ) = 0)) (PreH29 : (2 <= segments)) (PreH30 : (segments <= (i + 2 ))) (PreH31 : (old = (Zlength (base_products)))) (PreH32 : (base_products = (sublist (0) (old) (old_products)))) (PreH33 : (count = 1)) (PreH34 : (1 <= count)) (PreH35 : (count <= x_pre)) (PreH36 : (reaches = 1)) (PreH37 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH38 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH39 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH40 : (ValuableClosureState x_pre segment v base_products old old_products 1 )) (PreH41 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH42 : (ValuableBitmap x_pre (cons (1) ((@nil Z))) bitmap_2 )),
  (IntArray.seg products_buf 0 (count + 1 ) (cons (1) ((cons (v) ((@nil Z))))) )
  **  (IntArray.undef_seg products_buf (count + 1 ) (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) (replace_Znth (v) (1) (bitmap_2)) )
  **  (IntArray.full a_pre n_pre values )
|--
  EX (bitmap: (@list Z)) (products: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= ((i + 1 ) + 1 )) ”
  &&  “ ((count + 1 ) = (Zlength (products))) ”
  &&  “ (1 <= (count + 1 )) ”
  &&  “ ((count + 1 ) <= x_pre) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (count + 1 ))) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values (i + 1 ) segments products ) ”
  &&  “ (ValuableForcedHistory x_pre values (i + 1 ) segments products ) ”
  &&  “ (ValuableAlignedHistory x_pre values (i + 1 ) segments products ) ”
  &&  “ (ValuableBitmap x_pre products bitmap ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 (count + 1 ) products )
  **  (IntArray.undef_seg products_buf (count + 1 ) (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (old_products: (@list Z)) (bitmap_2: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (PreH1 : ((Znth v bitmap_2 0) = 0)) (PreH2 : (0 <= v)) (PreH3 : (v < (x_pre + 1 ))) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (count <= INT_MAX)) (PreH6 : (old <= INT_MAX)) (PreH7 : (segments <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (reaches >= INT_MIN)) (PreH11 : (count >= INT_MIN)) (PreH12 : (old >= INT_MIN)) (PreH13 : (segments >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (2 <= x_pre)) (PreH18 : (x_pre <= 100000)) (PreH19 : (1 <= (Zlength (values)))) (PreH20 : ((Zlength (values)) <= 100000)) (PreH21 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 200000)))) (PreH22 : (Pre x_pre values )) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (v = (Znth i values 0))) (PreH26 : (1 <= v)) (PreH27 : (v <= x_pre)) (PreH28 : ((x_pre % ( v ) ) = 0)) (PreH29 : (2 <= segments)) (PreH30 : (segments <= (i + 2 ))) (PreH31 : (old = (Zlength (base_products)))) (PreH32 : (base_products = (sublist (0) (old) (old_products)))) (PreH33 : (count = 1)) (PreH34 : (1 <= count)) (PreH35 : (count <= x_pre)) (PreH36 : (reaches = 1)) (PreH37 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH38 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH39 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH40 : (ValuableClosureState x_pre segment v base_products old old_products 1 )) (PreH41 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH42 : (ValuableBitmap x_pre (cons (1) ((@nil Z))) bitmap_2 )),
  TT && emp 
|--
  “ (ValuableBitmap x_pre (cons (1) ((cons (v) ((@nil Z))))) (replace_Znth (v) (1) (bitmap_2)) ) ”
  &&  “ (ValuableAlignedHistory x_pre values (i + 1 ) segments (cons (1) ((cons (v) ((@nil Z))))) ) ”
  &&  “ (ValuableForcedHistory x_pre values (i + 1 ) segments (cons (1) ((cons (v) ((@nil Z))))) ) ”
  &&  “ (ValuableOuterState x_pre values (i + 1 ) segments (cons (1) ((cons (v) ((@nil Z))))) ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (count + 1 ))) -> ((1 <= (Znth k_2 (cons (1) ((cons (v) ((@nil Z))))) 0)) /\ ((Znth k_2 (cons (1) ((cons (v) ((@nil Z))))) 0) <= x_pre))) ”
  &&  “ ((Zlength ((replace_Znth (v) (1) (bitmap_2)))) = (x_pre + 1 )) ”
  &&  “ ((1 + 1 ) = (Zlength ((cons (1) ((cons (v) ((@nil Z)))))))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  emp
).

Definition solver_entail_wit_14_1_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (old_products: (@list Z)) (bitmap_2: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (PreH1 : ((Znth v bitmap_2 0) = 0)) (PreH2 : (0 <= v)) (PreH3 : (v < (x_pre + 1 ))) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (count <= INT_MAX)) (PreH6 : (old <= INT_MAX)) (PreH7 : (segments <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (reaches >= INT_MIN)) (PreH11 : (count >= INT_MIN)) (PreH12 : (old >= INT_MIN)) (PreH13 : (segments >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (2 <= x_pre)) (PreH18 : (x_pre <= 100000)) (PreH19 : (1 <= (Zlength (values)))) (PreH20 : ((Zlength (values)) <= 100000)) (PreH21 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 200000)))) (PreH22 : (Pre x_pre values )) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (v = (Znth i values 0))) (PreH26 : (1 <= v)) (PreH27 : (v <= x_pre)) (PreH28 : ((x_pre % ( v ) ) = 0)) (PreH29 : (2 <= segments)) (PreH30 : (segments <= (i + 2 ))) (PreH31 : (old = (Zlength (base_products)))) (PreH32 : (base_products = (sublist (0) (old) (old_products)))) (PreH33 : (count = 1)) (PreH34 : (1 <= count)) (PreH35 : (count <= x_pre)) (PreH36 : (reaches = 1)) (PreH37 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH38 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH39 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH40 : (ValuableClosureState x_pre segment v base_products old old_products 1 )) (PreH41 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH42 : (ValuableBitmap x_pre (cons (1) ((@nil Z))) bitmap_2 )),
  (ValuableBitmap x_pre (cons (1) ((cons (v) ((@nil Z))))) (replace_Znth (v) (1) (bitmap_2)) )
.

Definition solver_entail_wit_14_1_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (old_products: (@list Z)) (bitmap_2: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (PreH1 : ((Znth v bitmap_2 0) = 0)) (PreH2 : (0 <= v)) (PreH3 : (v < (x_pre + 1 ))) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (count <= INT_MAX)) (PreH6 : (old <= INT_MAX)) (PreH7 : (segments <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (reaches >= INT_MIN)) (PreH11 : (count >= INT_MIN)) (PreH12 : (old >= INT_MIN)) (PreH13 : (segments >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (2 <= x_pre)) (PreH18 : (x_pre <= 100000)) (PreH19 : (1 <= (Zlength (values)))) (PreH20 : ((Zlength (values)) <= 100000)) (PreH21 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 200000)))) (PreH22 : (Pre x_pre values )) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (v = (Znth i values 0))) (PreH26 : (1 <= v)) (PreH27 : (v <= x_pre)) (PreH28 : ((x_pre % ( v ) ) = 0)) (PreH29 : (2 <= segments)) (PreH30 : (segments <= (i + 2 ))) (PreH31 : (old = (Zlength (base_products)))) (PreH32 : (base_products = (sublist (0) (old) (old_products)))) (PreH33 : (count = 1)) (PreH34 : (1 <= count)) (PreH35 : (count <= x_pre)) (PreH36 : (reaches = 1)) (PreH37 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH38 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH39 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH40 : (ValuableClosureState x_pre segment v base_products old old_products 1 )) (PreH41 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH42 : (ValuableBitmap x_pre (cons (1) ((@nil Z))) bitmap_2 )),
  (ValuableAlignedHistory x_pre values (i + 1 ) segments (cons (1) ((cons (v) ((@nil Z))))) )
.

Definition solver_entail_wit_14_1_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (old_products: (@list Z)) (bitmap_2: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (PreH1 : ((Znth v bitmap_2 0) = 0)) (PreH2 : (0 <= v)) (PreH3 : (v < (x_pre + 1 ))) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (count <= INT_MAX)) (PreH6 : (old <= INT_MAX)) (PreH7 : (segments <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (reaches >= INT_MIN)) (PreH11 : (count >= INT_MIN)) (PreH12 : (old >= INT_MIN)) (PreH13 : (segments >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (2 <= x_pre)) (PreH18 : (x_pre <= 100000)) (PreH19 : (1 <= (Zlength (values)))) (PreH20 : ((Zlength (values)) <= 100000)) (PreH21 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 200000)))) (PreH22 : (Pre x_pre values )) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (v = (Znth i values 0))) (PreH26 : (1 <= v)) (PreH27 : (v <= x_pre)) (PreH28 : ((x_pre % ( v ) ) = 0)) (PreH29 : (2 <= segments)) (PreH30 : (segments <= (i + 2 ))) (PreH31 : (old = (Zlength (base_products)))) (PreH32 : (base_products = (sublist (0) (old) (old_products)))) (PreH33 : (count = 1)) (PreH34 : (1 <= count)) (PreH35 : (count <= x_pre)) (PreH36 : (reaches = 1)) (PreH37 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH38 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH39 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH40 : (ValuableClosureState x_pre segment v base_products old old_products 1 )) (PreH41 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH42 : (ValuableBitmap x_pre (cons (1) ((@nil Z))) bitmap_2 )),
  (ValuableForcedHistory x_pre values (i + 1 ) segments (cons (1) ((cons (v) ((@nil Z))))) )
.

Definition solver_entail_wit_14_1_split_goal_4 :=
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (old_products: (@list Z)) (bitmap_2: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (PreH1 : ((Znth v bitmap_2 0) = 0)) (PreH2 : (0 <= v)) (PreH3 : (v < (x_pre + 1 ))) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (count <= INT_MAX)) (PreH6 : (old <= INT_MAX)) (PreH7 : (segments <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (reaches >= INT_MIN)) (PreH11 : (count >= INT_MIN)) (PreH12 : (old >= INT_MIN)) (PreH13 : (segments >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (2 <= x_pre)) (PreH18 : (x_pre <= 100000)) (PreH19 : (1 <= (Zlength (values)))) (PreH20 : ((Zlength (values)) <= 100000)) (PreH21 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 200000)))) (PreH22 : (Pre x_pre values )) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (v = (Znth i values 0))) (PreH26 : (1 <= v)) (PreH27 : (v <= x_pre)) (PreH28 : ((x_pre % ( v ) ) = 0)) (PreH29 : (2 <= segments)) (PreH30 : (segments <= (i + 2 ))) (PreH31 : (old = (Zlength (base_products)))) (PreH32 : (base_products = (sublist (0) (old) (old_products)))) (PreH33 : (count = 1)) (PreH34 : (1 <= count)) (PreH35 : (count <= x_pre)) (PreH36 : (reaches = 1)) (PreH37 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH38 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH39 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH40 : (ValuableClosureState x_pre segment v base_products old old_products 1 )) (PreH41 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH42 : (ValuableBitmap x_pre (cons (1) ((@nil Z))) bitmap_2 )),
  (ValuableOuterState x_pre values (i + 1 ) segments (cons (1) ((cons (v) ((@nil Z))))) )
.

Definition solver_entail_wit_14_1_split_goal_5 :=
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (old_products: (@list Z)) (bitmap_2: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (PreH1 : ((Znth v bitmap_2 0) = 0)) (PreH2 : (0 <= v)) (PreH3 : (v < (x_pre + 1 ))) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (count <= INT_MAX)) (PreH6 : (old <= INT_MAX)) (PreH7 : (segments <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (reaches >= INT_MIN)) (PreH11 : (count >= INT_MIN)) (PreH12 : (old >= INT_MIN)) (PreH13 : (segments >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (2 <= x_pre)) (PreH18 : (x_pre <= 100000)) (PreH19 : (1 <= (Zlength (values)))) (PreH20 : ((Zlength (values)) <= 100000)) (PreH21 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 200000)))) (PreH22 : (Pre x_pre values )) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (v = (Znth i values 0))) (PreH26 : (1 <= v)) (PreH27 : (v <= x_pre)) (PreH28 : ((x_pre % ( v ) ) = 0)) (PreH29 : (2 <= segments)) (PreH30 : (segments <= (i + 2 ))) (PreH31 : (old = (Zlength (base_products)))) (PreH32 : (base_products = (sublist (0) (old) (old_products)))) (PreH33 : (count = 1)) (PreH34 : (1 <= count)) (PreH35 : (count <= x_pre)) (PreH36 : (reaches = 1)) (PreH37 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH38 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH39 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH40 : (ValuableClosureState x_pre segment v base_products old old_products 1 )) (PreH41 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH42 : (ValuableBitmap x_pre (cons (1) ((@nil Z))) bitmap_2 )),
  forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (count + 1 ))) -> ((1 <= (Znth k_2 (cons (1) ((cons (v) ((@nil Z))))) 0)) /\ ((Znth k_2 (cons (1) ((cons (v) ((@nil Z))))) 0) <= x_pre)))
.

Definition solver_entail_wit_14_1_split_goal_6 :=
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (old_products: (@list Z)) (bitmap_2: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (PreH1 : ((Znth v bitmap_2 0) = 0)) (PreH2 : (0 <= v)) (PreH3 : (v < (x_pre + 1 ))) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (count <= INT_MAX)) (PreH6 : (old <= INT_MAX)) (PreH7 : (segments <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (reaches >= INT_MIN)) (PreH11 : (count >= INT_MIN)) (PreH12 : (old >= INT_MIN)) (PreH13 : (segments >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (2 <= x_pre)) (PreH18 : (x_pre <= 100000)) (PreH19 : (1 <= (Zlength (values)))) (PreH20 : ((Zlength (values)) <= 100000)) (PreH21 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 200000)))) (PreH22 : (Pre x_pre values )) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (v = (Znth i values 0))) (PreH26 : (1 <= v)) (PreH27 : (v <= x_pre)) (PreH28 : ((x_pre % ( v ) ) = 0)) (PreH29 : (2 <= segments)) (PreH30 : (segments <= (i + 2 ))) (PreH31 : (old = (Zlength (base_products)))) (PreH32 : (base_products = (sublist (0) (old) (old_products)))) (PreH33 : (count = 1)) (PreH34 : (1 <= count)) (PreH35 : (count <= x_pre)) (PreH36 : (reaches = 1)) (PreH37 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH38 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH39 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH40 : (ValuableClosureState x_pre segment v base_products old old_products 1 )) (PreH41 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH42 : (ValuableBitmap x_pre (cons (1) ((@nil Z))) bitmap_2 )),
  ((Zlength ((replace_Znth (v) (1) (bitmap_2)))) = (x_pre + 1 ))
.

Definition solver_entail_wit_14_1_split_goal_7 :=
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (old_products: (@list Z)) (bitmap_2: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (PreH1 : ((Znth v bitmap_2 0) = 0)) (PreH2 : (0 <= v)) (PreH3 : (v < (x_pre + 1 ))) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (count <= INT_MAX)) (PreH6 : (old <= INT_MAX)) (PreH7 : (segments <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (reaches >= INT_MIN)) (PreH11 : (count >= INT_MIN)) (PreH12 : (old >= INT_MIN)) (PreH13 : (segments >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (2 <= x_pre)) (PreH18 : (x_pre <= 100000)) (PreH19 : (1 <= (Zlength (values)))) (PreH20 : ((Zlength (values)) <= 100000)) (PreH21 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 200000)))) (PreH22 : (Pre x_pre values )) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (v = (Znth i values 0))) (PreH26 : (1 <= v)) (PreH27 : (v <= x_pre)) (PreH28 : ((x_pre % ( v ) ) = 0)) (PreH29 : (2 <= segments)) (PreH30 : (segments <= (i + 2 ))) (PreH31 : (old = (Zlength (base_products)))) (PreH32 : (base_products = (sublist (0) (old) (old_products)))) (PreH33 : (count = 1)) (PreH34 : (1 <= count)) (PreH35 : (count <= x_pre)) (PreH36 : (reaches = 1)) (PreH37 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH38 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH39 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH40 : (ValuableClosureState x_pre segment v base_products old old_products 1 )) (PreH41 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH42 : (ValuableBitmap x_pre (cons (1) ((@nil Z))) bitmap_2 )),
  ((1 + 1 ) = (Zlength ((cons (1) ((cons (v) ((@nil Z))))))))
.

Definition solver_entail_wit_14_1_split_goal_8 :=
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (old_products: (@list Z)) (bitmap_2: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (PreH1 : ((Znth v bitmap_2 0) = 0)) (PreH2 : (0 <= v)) (PreH3 : (v < (x_pre + 1 ))) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (count <= INT_MAX)) (PreH6 : (old <= INT_MAX)) (PreH7 : (segments <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (reaches >= INT_MIN)) (PreH11 : (count >= INT_MIN)) (PreH12 : (old >= INT_MIN)) (PreH13 : (segments >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (2 <= x_pre)) (PreH18 : (x_pre <= 100000)) (PreH19 : (1 <= (Zlength (values)))) (PreH20 : ((Zlength (values)) <= 100000)) (PreH21 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 200000)))) (PreH22 : (Pre x_pre values )) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (v = (Znth i values 0))) (PreH26 : (1 <= v)) (PreH27 : (v <= x_pre)) (PreH28 : ((x_pre % ( v ) ) = 0)) (PreH29 : (2 <= segments)) (PreH30 : (segments <= (i + 2 ))) (PreH31 : (old = (Zlength (base_products)))) (PreH32 : (base_products = (sublist (0) (old) (old_products)))) (PreH33 : (count = 1)) (PreH34 : (1 <= count)) (PreH35 : (count <= x_pre)) (PreH36 : (reaches = 1)) (PreH37 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH38 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH39 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH40 : (ValuableClosureState x_pre segment v base_products old old_products 1 )) (PreH41 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH42 : (ValuableBitmap x_pre (cons (1) ((@nil Z))) bitmap_2 )),
  forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))
.

Definition solver_entail_wit_14_2 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (old_products: (@list Z)) (bitmap_2: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (products_buf: Z) (used: Z) (PreH1 : ((Znth v bitmap_2 0) <> 0)) (PreH2 : (0 <= v)) (PreH3 : (v < (x_pre + 1 ))) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (count <= INT_MAX)) (PreH6 : (old <= INT_MAX)) (PreH7 : (segments <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (reaches >= INT_MIN)) (PreH11 : (count >= INT_MIN)) (PreH12 : (old >= INT_MIN)) (PreH13 : (segments >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (2 <= x_pre)) (PreH18 : (x_pre <= 100000)) (PreH19 : (1 <= (Zlength (values)))) (PreH20 : ((Zlength (values)) <= 100000)) (PreH21 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 200000)))) (PreH22 : (Pre x_pre values )) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (v = (Znth i values 0))) (PreH26 : (1 <= v)) (PreH27 : (v <= x_pre)) (PreH28 : ((x_pre % ( v ) ) = 0)) (PreH29 : (2 <= segments)) (PreH30 : (segments <= (i + 2 ))) (PreH31 : (old = (Zlength (base_products)))) (PreH32 : (base_products = (sublist (0) (old) (old_products)))) (PreH33 : (count = 1)) (PreH34 : (1 <= count)) (PreH35 : (count <= x_pre)) (PreH36 : (reaches = 1)) (PreH37 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH38 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH39 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH40 : (ValuableClosureState x_pre segment v base_products old old_products 1 )) (PreH41 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH42 : (ValuableBitmap x_pre (cons (1) ((@nil Z))) bitmap_2 )),
  (UCharArray.full used (x_pre + 1 ) bitmap_2 )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count (cons (1) ((@nil Z))) )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
|--
  EX (bitmap: (@list Z)) (products: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= ((i + 1 ) + 1 )) ”
  &&  “ (count = (Zlength (products))) ”
  &&  “ (1 <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values (i + 1 ) segments products ) ”
  &&  “ (ValuableForcedHistory x_pre values (i + 1 ) segments products ) ”
  &&  “ (ValuableAlignedHistory x_pre values (i + 1 ) segments products ) ”
  &&  “ (ValuableBitmap x_pre products bitmap ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (old_products: (@list Z)) (bitmap_2: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (PreH1 : ((Znth v bitmap_2 0) <> 0)) (PreH2 : (0 <= v)) (PreH3 : (v < (x_pre + 1 ))) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (count <= INT_MAX)) (PreH6 : (old <= INT_MAX)) (PreH7 : (segments <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (reaches >= INT_MIN)) (PreH11 : (count >= INT_MIN)) (PreH12 : (old >= INT_MIN)) (PreH13 : (segments >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (2 <= x_pre)) (PreH18 : (x_pre <= 100000)) (PreH19 : (1 <= (Zlength (values)))) (PreH20 : ((Zlength (values)) <= 100000)) (PreH21 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 200000)))) (PreH22 : (Pre x_pre values )) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (v = (Znth i values 0))) (PreH26 : (1 <= v)) (PreH27 : (v <= x_pre)) (PreH28 : ((x_pre % ( v ) ) = 0)) (PreH29 : (2 <= segments)) (PreH30 : (segments <= (i + 2 ))) (PreH31 : (old = (Zlength (base_products)))) (PreH32 : (base_products = (sublist (0) (old) (old_products)))) (PreH33 : (count = 1)) (PreH34 : (1 <= count)) (PreH35 : (count <= x_pre)) (PreH36 : (reaches = 1)) (PreH37 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH38 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH39 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH40 : (ValuableClosureState x_pre segment v base_products old old_products 1 )) (PreH41 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH42 : (ValuableBitmap x_pre (cons (1) ((@nil Z))) bitmap_2 )),
  TT && emp 
|--
  “ (ValuableAlignedHistory x_pre values (i + 1 ) segments (cons (1) ((@nil Z))) ) ”
  &&  “ (ValuableForcedHistory x_pre values (i + 1 ) segments (cons (1) ((@nil Z))) ) ”
  &&  “ (ValuableOuterState x_pre values (i + 1 ) segments (cons (1) ((@nil Z))) ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 (cons (1) ((@nil Z))) 0)) /\ ((Znth k_2 (cons (1) ((@nil Z))) 0) <= x_pre))) ”
  &&  “ (1 = (Zlength ((cons (1) ((@nil Z)))))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  emp
).

Definition solver_entail_wit_14_2_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (old_products: (@list Z)) (bitmap_2: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (PreH1 : ((Znth v bitmap_2 0) <> 0)) (PreH2 : (0 <= v)) (PreH3 : (v < (x_pre + 1 ))) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (count <= INT_MAX)) (PreH6 : (old <= INT_MAX)) (PreH7 : (segments <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (reaches >= INT_MIN)) (PreH11 : (count >= INT_MIN)) (PreH12 : (old >= INT_MIN)) (PreH13 : (segments >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (2 <= x_pre)) (PreH18 : (x_pre <= 100000)) (PreH19 : (1 <= (Zlength (values)))) (PreH20 : ((Zlength (values)) <= 100000)) (PreH21 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 200000)))) (PreH22 : (Pre x_pre values )) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (v = (Znth i values 0))) (PreH26 : (1 <= v)) (PreH27 : (v <= x_pre)) (PreH28 : ((x_pre % ( v ) ) = 0)) (PreH29 : (2 <= segments)) (PreH30 : (segments <= (i + 2 ))) (PreH31 : (old = (Zlength (base_products)))) (PreH32 : (base_products = (sublist (0) (old) (old_products)))) (PreH33 : (count = 1)) (PreH34 : (1 <= count)) (PreH35 : (count <= x_pre)) (PreH36 : (reaches = 1)) (PreH37 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH38 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH39 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH40 : (ValuableClosureState x_pre segment v base_products old old_products 1 )) (PreH41 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH42 : (ValuableBitmap x_pre (cons (1) ((@nil Z))) bitmap_2 )),
  (ValuableAlignedHistory x_pre values (i + 1 ) segments (cons (1) ((@nil Z))) )
.

Definition solver_entail_wit_14_2_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (old_products: (@list Z)) (bitmap_2: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (PreH1 : ((Znth v bitmap_2 0) <> 0)) (PreH2 : (0 <= v)) (PreH3 : (v < (x_pre + 1 ))) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (count <= INT_MAX)) (PreH6 : (old <= INT_MAX)) (PreH7 : (segments <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (reaches >= INT_MIN)) (PreH11 : (count >= INT_MIN)) (PreH12 : (old >= INT_MIN)) (PreH13 : (segments >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (2 <= x_pre)) (PreH18 : (x_pre <= 100000)) (PreH19 : (1 <= (Zlength (values)))) (PreH20 : ((Zlength (values)) <= 100000)) (PreH21 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 200000)))) (PreH22 : (Pre x_pre values )) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (v = (Znth i values 0))) (PreH26 : (1 <= v)) (PreH27 : (v <= x_pre)) (PreH28 : ((x_pre % ( v ) ) = 0)) (PreH29 : (2 <= segments)) (PreH30 : (segments <= (i + 2 ))) (PreH31 : (old = (Zlength (base_products)))) (PreH32 : (base_products = (sublist (0) (old) (old_products)))) (PreH33 : (count = 1)) (PreH34 : (1 <= count)) (PreH35 : (count <= x_pre)) (PreH36 : (reaches = 1)) (PreH37 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH38 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH39 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH40 : (ValuableClosureState x_pre segment v base_products old old_products 1 )) (PreH41 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH42 : (ValuableBitmap x_pre (cons (1) ((@nil Z))) bitmap_2 )),
  (ValuableForcedHistory x_pre values (i + 1 ) segments (cons (1) ((@nil Z))) )
.

Definition solver_entail_wit_14_2_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (old_products: (@list Z)) (bitmap_2: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (PreH1 : ((Znth v bitmap_2 0) <> 0)) (PreH2 : (0 <= v)) (PreH3 : (v < (x_pre + 1 ))) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (count <= INT_MAX)) (PreH6 : (old <= INT_MAX)) (PreH7 : (segments <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (reaches >= INT_MIN)) (PreH11 : (count >= INT_MIN)) (PreH12 : (old >= INT_MIN)) (PreH13 : (segments >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (2 <= x_pre)) (PreH18 : (x_pre <= 100000)) (PreH19 : (1 <= (Zlength (values)))) (PreH20 : ((Zlength (values)) <= 100000)) (PreH21 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 200000)))) (PreH22 : (Pre x_pre values )) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (v = (Znth i values 0))) (PreH26 : (1 <= v)) (PreH27 : (v <= x_pre)) (PreH28 : ((x_pre % ( v ) ) = 0)) (PreH29 : (2 <= segments)) (PreH30 : (segments <= (i + 2 ))) (PreH31 : (old = (Zlength (base_products)))) (PreH32 : (base_products = (sublist (0) (old) (old_products)))) (PreH33 : (count = 1)) (PreH34 : (1 <= count)) (PreH35 : (count <= x_pre)) (PreH36 : (reaches = 1)) (PreH37 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH38 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH39 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH40 : (ValuableClosureState x_pre segment v base_products old old_products 1 )) (PreH41 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH42 : (ValuableBitmap x_pre (cons (1) ((@nil Z))) bitmap_2 )),
  (ValuableOuterState x_pre values (i + 1 ) segments (cons (1) ((@nil Z))) )
.

Definition solver_entail_wit_14_2_split_goal_4 :=
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (old_products: (@list Z)) (bitmap_2: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (PreH1 : ((Znth v bitmap_2 0) <> 0)) (PreH2 : (0 <= v)) (PreH3 : (v < (x_pre + 1 ))) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (count <= INT_MAX)) (PreH6 : (old <= INT_MAX)) (PreH7 : (segments <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (reaches >= INT_MIN)) (PreH11 : (count >= INT_MIN)) (PreH12 : (old >= INT_MIN)) (PreH13 : (segments >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (2 <= x_pre)) (PreH18 : (x_pre <= 100000)) (PreH19 : (1 <= (Zlength (values)))) (PreH20 : ((Zlength (values)) <= 100000)) (PreH21 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 200000)))) (PreH22 : (Pre x_pre values )) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (v = (Znth i values 0))) (PreH26 : (1 <= v)) (PreH27 : (v <= x_pre)) (PreH28 : ((x_pre % ( v ) ) = 0)) (PreH29 : (2 <= segments)) (PreH30 : (segments <= (i + 2 ))) (PreH31 : (old = (Zlength (base_products)))) (PreH32 : (base_products = (sublist (0) (old) (old_products)))) (PreH33 : (count = 1)) (PreH34 : (1 <= count)) (PreH35 : (count <= x_pre)) (PreH36 : (reaches = 1)) (PreH37 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH38 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH39 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH40 : (ValuableClosureState x_pre segment v base_products old old_products 1 )) (PreH41 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH42 : (ValuableBitmap x_pre (cons (1) ((@nil Z))) bitmap_2 )),
  forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 (cons (1) ((@nil Z))) 0)) /\ ((Znth k_2 (cons (1) ((@nil Z))) 0) <= x_pre)))
.

Definition solver_entail_wit_14_2_split_goal_5 :=
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (old_products: (@list Z)) (bitmap_2: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (PreH1 : ((Znth v bitmap_2 0) <> 0)) (PreH2 : (0 <= v)) (PreH3 : (v < (x_pre + 1 ))) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (count <= INT_MAX)) (PreH6 : (old <= INT_MAX)) (PreH7 : (segments <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (reaches >= INT_MIN)) (PreH11 : (count >= INT_MIN)) (PreH12 : (old >= INT_MIN)) (PreH13 : (segments >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (2 <= x_pre)) (PreH18 : (x_pre <= 100000)) (PreH19 : (1 <= (Zlength (values)))) (PreH20 : ((Zlength (values)) <= 100000)) (PreH21 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 200000)))) (PreH22 : (Pre x_pre values )) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (v = (Znth i values 0))) (PreH26 : (1 <= v)) (PreH27 : (v <= x_pre)) (PreH28 : ((x_pre % ( v ) ) = 0)) (PreH29 : (2 <= segments)) (PreH30 : (segments <= (i + 2 ))) (PreH31 : (old = (Zlength (base_products)))) (PreH32 : (base_products = (sublist (0) (old) (old_products)))) (PreH33 : (count = 1)) (PreH34 : (1 <= count)) (PreH35 : (count <= x_pre)) (PreH36 : (reaches = 1)) (PreH37 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH38 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH39 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH40 : (ValuableClosureState x_pre segment v base_products old old_products 1 )) (PreH41 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH42 : (ValuableBitmap x_pre (cons (1) ((@nil Z))) bitmap_2 )),
  (1 = (Zlength ((cons (1) ((@nil Z))))))
.

Definition solver_entail_wit_14_2_split_goal_6 :=
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (old_products: (@list Z)) (bitmap_2: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (PreH1 : ((Znth v bitmap_2 0) <> 0)) (PreH2 : (0 <= v)) (PreH3 : (v < (x_pre + 1 ))) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (count <= INT_MAX)) (PreH6 : (old <= INT_MAX)) (PreH7 : (segments <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (reaches >= INT_MIN)) (PreH11 : (count >= INT_MIN)) (PreH12 : (old >= INT_MIN)) (PreH13 : (segments >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (2 <= x_pre)) (PreH18 : (x_pre <= 100000)) (PreH19 : (1 <= (Zlength (values)))) (PreH20 : ((Zlength (values)) <= 100000)) (PreH21 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 200000)))) (PreH22 : (Pre x_pre values )) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (v = (Znth i values 0))) (PreH26 : (1 <= v)) (PreH27 : (v <= x_pre)) (PreH28 : ((x_pre % ( v ) ) = 0)) (PreH29 : (2 <= segments)) (PreH30 : (segments <= (i + 2 ))) (PreH31 : (old = (Zlength (base_products)))) (PreH32 : (base_products = (sublist (0) (old) (old_products)))) (PreH33 : (count = 1)) (PreH34 : (1 <= count)) (PreH35 : (count <= x_pre)) (PreH36 : (reaches = 1)) (PreH37 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH38 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH39 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH40 : (ValuableClosureState x_pre segment v base_products old old_products 1 )) (PreH41 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH42 : (ValuableBitmap x_pre (cons (1) ((@nil Z))) bitmap_2 )),
  forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))
.

Definition solver_entail_wit_14_3 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (products_2: (@list Z)) (bitmap_2: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (products_buf: Z) (used: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 200000)))) (PreH7 : (Pre x_pre values )) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (v = (Znth i values 0))) (PreH11 : (1 <= v)) (PreH12 : (v <= x_pre)) (PreH13 : ((x_pre % ( v ) ) = 0)) (PreH14 : (1 <= segments)) (PreH15 : (segments <= (i + 1 ))) (PreH16 : (old = (Zlength (base_products)))) (PreH17 : (base_products = (sublist (0) (old) (products_2)))) (PreH18 : (1 <= old)) (PreH19 : (old <= count)) (PreH20 : (count <= x_pre)) (PreH21 : (count = (Zlength (products_2)))) (PreH22 : (reaches = 0)) (PreH23 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH24 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < count)) -> ((1 <= (Znth k_4 products_2 0)) /\ ((Znth k_4 products_2 0) <= x_pre)))) (PreH25 : (ValuableOuterState x_pre values i segments base_products )) (PreH26 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH27 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH28 : (ValuableClosureState x_pre segment v base_products old products_2 reaches )) (PreH29 : (ValuableBitmap x_pre products_2 bitmap_2 )) (PreH30 : (reaches = 0)),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products_2 )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap_2 )
|--
  EX (bitmap: (@list Z)) (products: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= ((i + 1 ) + 1 )) ”
  &&  “ (count = (Zlength (products))) ”
  &&  “ (1 <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values (i + 1 ) segments products ) ”
  &&  “ (ValuableForcedHistory x_pre values (i + 1 ) segments products ) ”
  &&  “ (ValuableAlignedHistory x_pre values (i + 1 ) segments products ) ”
  &&  “ (ValuableBitmap x_pre products bitmap ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (products_2: (@list Z)) (bitmap_2: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 200000)))) (PreH7 : (Pre x_pre values )) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (v = (Znth i values 0))) (PreH11 : (1 <= v)) (PreH12 : (v <= x_pre)) (PreH13 : ((x_pre % ( v ) ) = 0)) (PreH14 : (1 <= segments)) (PreH15 : (segments <= (i + 1 ))) (PreH16 : (old = (Zlength (base_products)))) (PreH17 : (base_products = (sublist (0) (old) (products_2)))) (PreH18 : (1 <= old)) (PreH19 : (old <= count)) (PreH20 : (count <= x_pre)) (PreH21 : (count = (Zlength (products_2)))) (PreH22 : (reaches = 0)) (PreH23 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH24 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < count)) -> ((1 <= (Znth k_4 products_2 0)) /\ ((Znth k_4 products_2 0) <= x_pre)))) (PreH25 : (ValuableOuterState x_pre values i segments base_products )) (PreH26 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH27 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH28 : (ValuableClosureState x_pre segment v base_products old products_2 reaches )) (PreH29 : (ValuableBitmap x_pre products_2 bitmap_2 )) (PreH30 : (reaches = 0)),
  TT && emp 
|--
  “ (ValuableAlignedHistory x_pre values (i + 1 ) segments products_2 ) ”
  &&  “ (ValuableForcedHistory x_pre values (i + 1 ) segments products_2 ) ”
  &&  “ (ValuableOuterState x_pre values (i + 1 ) segments products_2 ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_2 0)) /\ ((Znth k_2 products_2 0) <= x_pre))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  emp
).

Definition solver_entail_wit_14_3_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (products_2: (@list Z)) (bitmap_2: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 200000)))) (PreH7 : (Pre x_pre values )) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (v = (Znth i values 0))) (PreH11 : (1 <= v)) (PreH12 : (v <= x_pre)) (PreH13 : ((x_pre % ( v ) ) = 0)) (PreH14 : (1 <= segments)) (PreH15 : (segments <= (i + 1 ))) (PreH16 : (old = (Zlength (base_products)))) (PreH17 : (base_products = (sublist (0) (old) (products_2)))) (PreH18 : (1 <= old)) (PreH19 : (old <= count)) (PreH20 : (count <= x_pre)) (PreH21 : (count = (Zlength (products_2)))) (PreH22 : (reaches = 0)) (PreH23 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH24 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < count)) -> ((1 <= (Znth k_4 products_2 0)) /\ ((Znth k_4 products_2 0) <= x_pre)))) (PreH25 : (ValuableOuterState x_pre values i segments base_products )) (PreH26 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH27 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH28 : (ValuableClosureState x_pre segment v base_products old products_2 reaches )) (PreH29 : (ValuableBitmap x_pre products_2 bitmap_2 )) (PreH30 : (reaches = 0)),
  (ValuableAlignedHistory x_pre values (i + 1 ) segments products_2 )
.

Definition solver_entail_wit_14_3_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (products_2: (@list Z)) (bitmap_2: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 200000)))) (PreH7 : (Pre x_pre values )) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (v = (Znth i values 0))) (PreH11 : (1 <= v)) (PreH12 : (v <= x_pre)) (PreH13 : ((x_pre % ( v ) ) = 0)) (PreH14 : (1 <= segments)) (PreH15 : (segments <= (i + 1 ))) (PreH16 : (old = (Zlength (base_products)))) (PreH17 : (base_products = (sublist (0) (old) (products_2)))) (PreH18 : (1 <= old)) (PreH19 : (old <= count)) (PreH20 : (count <= x_pre)) (PreH21 : (count = (Zlength (products_2)))) (PreH22 : (reaches = 0)) (PreH23 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH24 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < count)) -> ((1 <= (Znth k_4 products_2 0)) /\ ((Znth k_4 products_2 0) <= x_pre)))) (PreH25 : (ValuableOuterState x_pre values i segments base_products )) (PreH26 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH27 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH28 : (ValuableClosureState x_pre segment v base_products old products_2 reaches )) (PreH29 : (ValuableBitmap x_pre products_2 bitmap_2 )) (PreH30 : (reaches = 0)),
  (ValuableForcedHistory x_pre values (i + 1 ) segments products_2 )
.

Definition solver_entail_wit_14_3_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (products_2: (@list Z)) (bitmap_2: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 200000)))) (PreH7 : (Pre x_pre values )) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (v = (Znth i values 0))) (PreH11 : (1 <= v)) (PreH12 : (v <= x_pre)) (PreH13 : ((x_pre % ( v ) ) = 0)) (PreH14 : (1 <= segments)) (PreH15 : (segments <= (i + 1 ))) (PreH16 : (old = (Zlength (base_products)))) (PreH17 : (base_products = (sublist (0) (old) (products_2)))) (PreH18 : (1 <= old)) (PreH19 : (old <= count)) (PreH20 : (count <= x_pre)) (PreH21 : (count = (Zlength (products_2)))) (PreH22 : (reaches = 0)) (PreH23 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH24 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < count)) -> ((1 <= (Znth k_4 products_2 0)) /\ ((Znth k_4 products_2 0) <= x_pre)))) (PreH25 : (ValuableOuterState x_pre values i segments base_products )) (PreH26 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH27 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH28 : (ValuableClosureState x_pre segment v base_products old products_2 reaches )) (PreH29 : (ValuableBitmap x_pre products_2 bitmap_2 )) (PreH30 : (reaches = 0)),
  (ValuableOuterState x_pre values (i + 1 ) segments products_2 )
.

Definition solver_entail_wit_14_3_split_goal_4 :=
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (products_2: (@list Z)) (bitmap_2: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 200000)))) (PreH7 : (Pre x_pre values )) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (v = (Znth i values 0))) (PreH11 : (1 <= v)) (PreH12 : (v <= x_pre)) (PreH13 : ((x_pre % ( v ) ) = 0)) (PreH14 : (1 <= segments)) (PreH15 : (segments <= (i + 1 ))) (PreH16 : (old = (Zlength (base_products)))) (PreH17 : (base_products = (sublist (0) (old) (products_2)))) (PreH18 : (1 <= old)) (PreH19 : (old <= count)) (PreH20 : (count <= x_pre)) (PreH21 : (count = (Zlength (products_2)))) (PreH22 : (reaches = 0)) (PreH23 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH24 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < count)) -> ((1 <= (Znth k_4 products_2 0)) /\ ((Znth k_4 products_2 0) <= x_pre)))) (PreH25 : (ValuableOuterState x_pre values i segments base_products )) (PreH26 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH27 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH28 : (ValuableClosureState x_pre segment v base_products old products_2 reaches )) (PreH29 : (ValuableBitmap x_pre products_2 bitmap_2 )) (PreH30 : (reaches = 0)),
  forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_2 0)) /\ ((Znth k_2 products_2 0) <= x_pre)))
.

Definition solver_entail_wit_14_3_split_goal_5 :=
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (products_2: (@list Z)) (bitmap_2: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (2 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (values)))) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 200000)))) (PreH7 : (Pre x_pre values )) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (v = (Znth i values 0))) (PreH11 : (1 <= v)) (PreH12 : (v <= x_pre)) (PreH13 : ((x_pre % ( v ) ) = 0)) (PreH14 : (1 <= segments)) (PreH15 : (segments <= (i + 1 ))) (PreH16 : (old = (Zlength (base_products)))) (PreH17 : (base_products = (sublist (0) (old) (products_2)))) (PreH18 : (1 <= old)) (PreH19 : (old <= count)) (PreH20 : (count <= x_pre)) (PreH21 : (count = (Zlength (products_2)))) (PreH22 : (reaches = 0)) (PreH23 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH24 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < count)) -> ((1 <= (Znth k_4 products_2 0)) /\ ((Znth k_4 products_2 0) <= x_pre)))) (PreH25 : (ValuableOuterState x_pre values i segments base_products )) (PreH26 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH27 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH28 : (ValuableClosureState x_pre segment v base_products old products_2 reaches )) (PreH29 : (ValuableBitmap x_pre products_2 bitmap_2 )) (PreH30 : (reaches = 0)),
  forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))
.

Definition solver_entail_wit_14_4 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (bitmap_2: (@list Z)) (products_2: (@list Z)) (count: Z) (segments: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= segments)) (PreH12 : (segments <= (i + 1 ))) (PreH13 : (count = (Zlength (products_2)))) (PreH14 : (1 <= count)) (PreH15 : (count <= x_pre)) (PreH16 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH17 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_2 0)) /\ ((Znth k_2 products_2 0) <= x_pre)))) (PreH18 : (ValuableOuterState x_pre values i segments products_2 )) (PreH19 : (ValuableForcedHistory x_pre values i segments products_2 )) (PreH20 : (ValuableAlignedHistory x_pre values i segments products_2 )) (PreH21 : (ValuableBitmap x_pre products_2 bitmap_2 )) (PreH22 : ((x_pre % ( (Znth i values 0) ) ) <> 0)),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products_2 )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap_2 )
|--
  EX (bitmap: (@list Z)) (products: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= ((i + 1 ) + 1 )) ”
  &&  “ (count = (Zlength (products))) ”
  &&  “ (1 <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values (i + 1 ) segments products ) ”
  &&  “ (ValuableForcedHistory x_pre values (i + 1 ) segments products ) ”
  &&  “ (ValuableAlignedHistory x_pre values (i + 1 ) segments products ) ”
  &&  “ (ValuableBitmap x_pre products bitmap ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (bitmap_2: (@list Z)) (products_2: (@list Z)) (count: Z) (segments: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= segments)) (PreH12 : (segments <= (i + 1 ))) (PreH13 : (count = (Zlength (products_2)))) (PreH14 : (1 <= count)) (PreH15 : (count <= x_pre)) (PreH16 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH17 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_2 0)) /\ ((Znth k_2 products_2 0) <= x_pre)))) (PreH18 : (ValuableOuterState x_pre values i segments products_2 )) (PreH19 : (ValuableForcedHistory x_pre values i segments products_2 )) (PreH20 : (ValuableAlignedHistory x_pre values i segments products_2 )) (PreH21 : (ValuableBitmap x_pre products_2 bitmap_2 )) (PreH22 : ((x_pre % ( (Znth i values 0) ) ) <> 0)),
  TT && emp 
|--
  “ (ValuableAlignedHistory x_pre values (i + 1 ) segments products_2 ) ”
  &&  “ (ValuableForcedHistory x_pre values (i + 1 ) segments products_2 ) ”
  &&  “ (ValuableOuterState x_pre values (i + 1 ) segments products_2 ) ”
  &&  emp
).

Definition solver_entail_wit_14_4_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (bitmap_2: (@list Z)) (products_2: (@list Z)) (count: Z) (segments: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= segments)) (PreH12 : (segments <= (i + 1 ))) (PreH13 : (count = (Zlength (products_2)))) (PreH14 : (1 <= count)) (PreH15 : (count <= x_pre)) (PreH16 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH17 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_2 0)) /\ ((Znth k_2 products_2 0) <= x_pre)))) (PreH18 : (ValuableOuterState x_pre values i segments products_2 )) (PreH19 : (ValuableForcedHistory x_pre values i segments products_2 )) (PreH20 : (ValuableAlignedHistory x_pre values i segments products_2 )) (PreH21 : (ValuableBitmap x_pre products_2 bitmap_2 )) (PreH22 : ((x_pre % ( (Znth i values 0) ) ) <> 0)),
  (ValuableAlignedHistory x_pre values (i + 1 ) segments products_2 )
.

Definition solver_entail_wit_14_4_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (bitmap_2: (@list Z)) (products_2: (@list Z)) (count: Z) (segments: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= segments)) (PreH12 : (segments <= (i + 1 ))) (PreH13 : (count = (Zlength (products_2)))) (PreH14 : (1 <= count)) (PreH15 : (count <= x_pre)) (PreH16 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH17 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_2 0)) /\ ((Znth k_2 products_2 0) <= x_pre)))) (PreH18 : (ValuableOuterState x_pre values i segments products_2 )) (PreH19 : (ValuableForcedHistory x_pre values i segments products_2 )) (PreH20 : (ValuableAlignedHistory x_pre values i segments products_2 )) (PreH21 : (ValuableBitmap x_pre products_2 bitmap_2 )) (PreH22 : ((x_pre % ( (Znth i values 0) ) ) <> 0)),
  (ValuableForcedHistory x_pre values (i + 1 ) segments products_2 )
.

Definition solver_entail_wit_14_4_split_goal_3 :=
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (bitmap_2: (@list Z)) (products_2: (@list Z)) (count: Z) (segments: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= segments)) (PreH12 : (segments <= (i + 1 ))) (PreH13 : (count = (Zlength (products_2)))) (PreH14 : (1 <= count)) (PreH15 : (count <= x_pre)) (PreH16 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH17 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_2 0)) /\ ((Znth k_2 products_2 0) <= x_pre)))) (PreH18 : (ValuableOuterState x_pre values i segments products_2 )) (PreH19 : (ValuableForcedHistory x_pre values i segments products_2 )) (PreH20 : (ValuableAlignedHistory x_pre values i segments products_2 )) (PreH21 : (ValuableBitmap x_pre products_2 bitmap_2 )) (PreH22 : ((x_pre % ( (Znth i values 0) ) ) <> 0)),
  (ValuableOuterState x_pre values (i + 1 ) segments products_2 )
.

Definition solver_entail_wit_15 :=
(
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (bitmap_2: (@list Z)) (products_2: (@list Z)) (count: Z) (segments: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= segments)) (PreH12 : (segments <= (i + 1 ))) (PreH13 : (count = (Zlength (products_2)))) (PreH14 : (1 <= count)) (PreH15 : (count <= x_pre)) (PreH16 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH17 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_2 0)) /\ ((Znth k_2 products_2 0) <= x_pre)))) (PreH18 : (ValuableOuterState x_pre values i segments products_2 )) (PreH19 : (ValuableForcedHistory x_pre values i segments products_2 )) (PreH20 : (ValuableAlignedHistory x_pre values i segments products_2 )) (PreH21 : (ValuableBitmap x_pre products_2 bitmap_2 )),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products_2 )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap_2 )
|--
  EX (bitmap: (@list Z)) (products: (@list Z)),
  “ (n_pre = (Zlength (values))) ”
  &&  “ (Spec x_pre values segments ) ”
  &&  “ (ValuableAlignedHistory x_pre values n_pre segments products ) ”
  &&  “ (count = (Zlength (products))) ”
  &&  “ (1 <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
) \/
(
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (bitmap_2: (@list Z)) (products_2: (@list Z)) (count: Z) (segments: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= segments)) (PreH12 : (segments <= (i + 1 ))) (PreH13 : (count = (Zlength (products_2)))) (PreH14 : (1 <= count)) (PreH15 : (count <= x_pre)) (PreH16 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH17 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_2 0)) /\ ((Znth k_2 products_2 0) <= x_pre)))) (PreH18 : (ValuableOuterState x_pre values i segments products_2 )) (PreH19 : (ValuableForcedHistory x_pre values i segments products_2 )) (PreH20 : (ValuableAlignedHistory x_pre values i segments products_2 )) (PreH21 : (ValuableBitmap x_pre products_2 bitmap_2 )),
  TT && emp 
|--
  “ (ValuableAlignedHistory x_pre values n_pre segments products_2 ) ”
  &&  “ (Spec x_pre values segments ) ”
  &&  emp
).

Definition solver_entail_wit_15_split_goal_1 :=
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (bitmap_2: (@list Z)) (products_2: (@list Z)) (count: Z) (segments: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= segments)) (PreH12 : (segments <= (i + 1 ))) (PreH13 : (count = (Zlength (products_2)))) (PreH14 : (1 <= count)) (PreH15 : (count <= x_pre)) (PreH16 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH17 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_2 0)) /\ ((Znth k_2 products_2 0) <= x_pre)))) (PreH18 : (ValuableOuterState x_pre values i segments products_2 )) (PreH19 : (ValuableForcedHistory x_pre values i segments products_2 )) (PreH20 : (ValuableAlignedHistory x_pre values i segments products_2 )) (PreH21 : (ValuableBitmap x_pre products_2 bitmap_2 )),
  (ValuableAlignedHistory x_pre values n_pre segments products_2 )
.

Definition solver_entail_wit_15_split_goal_2 :=
forall (values: (@list Z)) (n_pre: Z) (x_pre: Z) (bitmap_2: (@list Z)) (products_2: (@list Z)) (count: Z) (segments: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= segments)) (PreH12 : (segments <= (i + 1 ))) (PreH13 : (count = (Zlength (products_2)))) (PreH14 : (1 <= count)) (PreH15 : (count <= x_pre)) (PreH16 : ((Zlength (bitmap_2)) = (x_pre + 1 ))) (PreH17 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_2 0)) /\ ((Znth k_2 products_2 0) <= x_pre)))) (PreH18 : (ValuableOuterState x_pre values i segments products_2 )) (PreH19 : (ValuableForcedHistory x_pre values i segments products_2 )) (PreH20 : (ValuableAlignedHistory x_pre values i segments products_2 )) (PreH21 : (ValuableBitmap x_pre products_2 bitmap_2 )),
  (Spec x_pre values segments )
.

Definition solver_return_wit_1 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (products: (@list Z)) (bitmap: (@list Z)) (segments: Z) (count: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (Spec x_pre values segments )) (PreH3 : (ValuableAlignedHistory x_pre values n_pre segments products )) (PreH4 : (count = (Zlength (products)))) (PreH5 : (1 <= count)) (PreH6 : (count <= x_pre)) (PreH7 : ((Zlength (bitmap)) = (x_pre + 1 ))),
  (IntArray.full a_pre n_pre values )
|--
  “ (Spec x_pre values segments ) ”
  &&  (IntArray.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_1_pure :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (PreH1 : (2 <= x_pre)) (PreH2 : (x_pre <= 100000)) (PreH3 : (1 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 100000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 200000)))) (PreH6 : (Pre x_pre values )) (PreH7 : (n_pre = (Zlength (values)))),
  ((( &( "used" ) )) # Ptr  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (0 <= (x_pre + 1 )) ”
  &&  “ ((x_pre + 1 ) <= INT_MAX) ”
  &&  “ ((x_pre + 1 ) = (x_pre + 1 )) ”
  &&  “ (1 = 1) ”
.

Definition solver_partial_solve_wit_1_aux :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (PreH1 : (2 <= x_pre)) (PreH2 : (x_pre <= 100000)) (PreH3 : (1 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 100000)) (PreH5 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 200000)))) (PreH6 : (Pre x_pre values )) (PreH7 : (n_pre = (Zlength (values)))),
  (IntArray.full a_pre n_pre values )
|--
  “ (0 <= (x_pre + 1 )) ”
  &&  “ ((x_pre + 1 ) <= INT_MAX) ”
  &&  “ ((x_pre + 1 ) = (x_pre + 1 )) ”
  &&  “ (1 = 1) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  (IntArray.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2_pure :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (2 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 200000)))) (PreH7 : (Pre x_pre values )) (PreH8 : (n_pre = (Zlength (values)))),
  ((( &( "products_buf" ) )) # Ptr  |->_)
  **  (UCharArray.full retval (x_pre + 1 ) (repeat_Z (0) ((x_pre + 1 ))) )
  **  ((( &( "used" ) )) # Ptr  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  (IntArray.full a_pre n_pre values )
|--
  “ (0 <= (x_pre + 1 )) ”
  &&  “ (((x_pre + 1 ) * sizeof(INT) ) = ((x_pre + 1 ) * sizeof(INT) )) ”
.

Definition solver_partial_solve_wit_2_aux :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (2 <= x_pre)) (PreH3 : (x_pre <= 100000)) (PreH4 : (1 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 100000)) (PreH6 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 200000)))) (PreH7 : (Pre x_pre values )) (PreH8 : (n_pre = (Zlength (values)))),
  (UCharArray.full retval (x_pre + 1 ) (repeat_Z (0) ((x_pre + 1 ))) )
  **  (IntArray.full a_pre n_pre values )
|--
  “ (0 <= (x_pre + 1 )) ”
  &&  “ (((x_pre + 1 ) * sizeof(INT) ) = ((x_pre + 1 ) * sizeof(INT) )) ”
  &&  “ (retval <> 0) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  (UCharArray.full retval (x_pre + 1 ) (repeat_Z (0) ((x_pre + 1 ))) )
  **  (IntArray.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_2 := solver_partial_solve_wit_2_pure -> solver_partial_solve_wit_2_aux.

Definition solver_partial_solve_wit_3 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (n_pre = (Zlength (values)))),
  (IntArray.undef_full retval_2 (x_pre + 1 ) )
  **  (UCharArray.full retval (x_pre + 1 ) (repeat_Z (0) ((x_pre + 1 ))) )
  **  (IntArray.full a_pre n_pre values )
|--
  “ (retval_2 <> 0) ”
  &&  “ (retval <> 0) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  (((retval_2 + (0 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg retval_2 1 (x_pre + 1 ) )
  **  (UCharArray.full retval (x_pre + 1 ) (repeat_Z (0) ((x_pre + 1 ))) )
  **  (IntArray.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_4 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (n_pre = (Zlength (values)))),
  (((retval_2 + (0 * sizeof(INT)))) # Int  |-> 1)
  **  (IntArray.undef_seg retval_2 1 (x_pre + 1 ) )
  **  (UCharArray.full retval (x_pre + 1 ) (repeat_Z (0) ((x_pre + 1 ))) )
  **  (IntArray.full a_pre n_pre values )
|--
  “ (retval_2 <> 0) ”
  &&  “ (retval <> 0) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  (((retval + (1 * sizeof(UCHAR)))) # UChar  |->_)
  **  (UCharArray.missing_i retval 1 0 (x_pre + 1 ) (repeat_Z (0) ((x_pre + 1 ))) )
  **  (((retval_2 + (0 * sizeof(INT)))) # Int  |-> 1)
  **  (IntArray.undef_seg retval_2 1 (x_pre + 1 ) )
  **  (IntArray.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_5 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (bitmap: (@list Z)) (products: (@list Z)) (count: Z) (segments: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= segments)) (PreH12 : (segments <= (i + 1 ))) (PreH13 : (count = (Zlength (products)))) (PreH14 : (1 <= count)) (PreH15 : (count <= x_pre)) (PreH16 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH17 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre)))) (PreH18 : (ValuableOuterState x_pre values i segments products )) (PreH19 : (ValuableForcedHistory x_pre values i segments products )) (PreH20 : (ValuableAlignedHistory x_pre values i segments products )) (PreH21 : (ValuableBitmap x_pre products bitmap )),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (i < n_pre) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (count = (Zlength (products))) ”
  &&  “ (1 <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments products ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments products ) ”
  &&  “ (ValuableBitmap x_pre products bitmap ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i values 0))
  **  (IntArray.missing_i a_pre i 0 n_pre values )
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
.

Definition solver_partial_solve_wit_6 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : (j < old)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (v = (Znth i values 0))) (PreH12 : (1 <= v)) (PreH13 : (v <= x_pre)) (PreH14 : ((x_pre % ( v ) ) = 0)) (PreH15 : (1 <= segments)) (PreH16 : (segments <= (i + 1 ))) (PreH17 : (old = (Zlength (base_products)))) (PreH18 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH19 : (1 <= old)) (PreH20 : (old <= count)) (PreH21 : (count <= x_pre)) (PreH22 : (0 <= j)) (PreH23 : (j <= old)) (PreH24 : (count = (Zlength (products_before_append)))) (PreH25 : (reaches = 1)) (PreH26 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH27 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH28 : (ValuableOuterState x_pre values i segments base_products )) (PreH29 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH30 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH31 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH32 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products_before_append )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (j < old) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products_before_append))) ”
  &&  “ (1 <= old) ”
  &&  “ (old <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= old) ”
  &&  “ (count = (Zlength (products_before_append))) ”
  &&  “ (reaches = 1) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products j products_before_append reaches ) ”
  &&  “ (ValuableBitmap x_pre products_before_append bitmap ) ”
  &&  (((products_buf + (j * sizeof(INT)))) # Int  |-> (Znth (j - 0 ) products_before_append 0))
  **  (IntArray.missing_i products_buf j 0 count products_before_append )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
.

Definition solver_partial_solve_wit_7 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : (j < old)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (v = (Znth i values 0))) (PreH12 : (1 <= v)) (PreH13 : (v <= x_pre)) (PreH14 : ((x_pre % ( v ) ) = 0)) (PreH15 : (1 <= segments)) (PreH16 : (segments <= (i + 1 ))) (PreH17 : (old = (Zlength (base_products)))) (PreH18 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH19 : (1 <= old)) (PreH20 : (old <= count)) (PreH21 : (count <= x_pre)) (PreH22 : (0 <= j)) (PreH23 : (j <= old)) (PreH24 : (count = (Zlength (products_before_append)))) (PreH25 : (reaches = 0)) (PreH26 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH27 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH28 : (ValuableOuterState x_pre values i segments base_products )) (PreH29 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH30 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH31 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH32 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products_before_append )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (j < old) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products_before_append))) ”
  &&  “ (1 <= old) ”
  &&  “ (old <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= old) ”
  &&  “ (count = (Zlength (products_before_append))) ”
  &&  “ (reaches = 0) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products j products_before_append reaches ) ”
  &&  “ (ValuableBitmap x_pre products_before_append bitmap ) ”
  &&  (((products_buf + (j * sizeof(INT)))) # Int  |-> (Znth (j - 0 ) products_before_append 0))
  **  (IntArray.missing_i products_buf j 0 count products_before_append )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
.

Definition solver_partial_solve_wit_8 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH2 : (j < old)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 100000)) (PreH6 : (1 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH9 : (Pre x_pre values )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (v = (Znth i values 0))) (PreH13 : (1 <= v)) (PreH14 : (v <= x_pre)) (PreH15 : ((x_pre % ( v ) ) = 0)) (PreH16 : (1 <= segments)) (PreH17 : (segments <= (i + 1 ))) (PreH18 : (old = (Zlength (base_products)))) (PreH19 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH20 : (1 <= old)) (PreH21 : (old <= count)) (PreH22 : (count <= x_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= old)) (PreH25 : (count = (Zlength (products_before_append)))) (PreH26 : (reaches = 0)) (PreH27 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH28 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH29 : (ValuableOuterState x_pre values i segments base_products )) (PreH30 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH31 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH32 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH33 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v )) ”
  &&  “ (j < old) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products_before_append))) ”
  &&  “ (1 <= old) ”
  &&  “ (old <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= old) ”
  &&  “ (count = (Zlength (products_before_append))) ”
  &&  “ (reaches = 0) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products j products_before_append reaches ) ”
  &&  “ (ValuableBitmap x_pre products_before_append bitmap ) ”
  &&  (((products_buf + (j * sizeof(INT)))) # Int  |-> (Znth (j - 0 ) products_before_append 0))
  **  (IntArray.missing_i products_buf j 0 count products_before_append )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
.

Definition solver_partial_solve_wit_9 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH2 : (j < old)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : (2 <= x_pre)) (PreH5 : (x_pre <= 100000)) (PreH6 : (1 <= (Zlength (values)))) (PreH7 : ((Zlength (values)) <= 100000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH9 : (Pre x_pre values )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (v = (Znth i values 0))) (PreH13 : (1 <= v)) (PreH14 : (v <= x_pre)) (PreH15 : ((x_pre % ( v ) ) = 0)) (PreH16 : (1 <= segments)) (PreH17 : (segments <= (i + 1 ))) (PreH18 : (old = (Zlength (base_products)))) (PreH19 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH20 : (1 <= old)) (PreH21 : (old <= count)) (PreH22 : (count <= x_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= old)) (PreH25 : (count = (Zlength (products_before_append)))) (PreH26 : (reaches = 1)) (PreH27 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH28 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH29 : (ValuableOuterState x_pre values i segments base_products )) (PreH30 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH31 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH32 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH33 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v )) ”
  &&  “ (j < old) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products_before_append))) ”
  &&  “ (1 <= old) ”
  &&  “ (old <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= old) ”
  &&  “ (count = (Zlength (products_before_append))) ”
  &&  “ (reaches = 1) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products j products_before_append reaches ) ”
  &&  “ (ValuableBitmap x_pre products_before_append bitmap ) ”
  &&  (((products_buf + (j * sizeof(INT)))) # Int  |-> (Znth (j - 0 ) products_before_append 0))
  **  (IntArray.missing_i products_buf j 0 count products_before_append )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
.

Definition solver_partial_solve_wit_10 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH2 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH3 : (j < old)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 100000)) (PreH7 : (1 <= (Zlength (values)))) (PreH8 : ((Zlength (values)) <= 100000)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH10 : (Pre x_pre values )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (v = (Znth i values 0))) (PreH14 : (1 <= v)) (PreH15 : (v <= x_pre)) (PreH16 : ((x_pre % ( v ) ) = 0)) (PreH17 : (1 <= segments)) (PreH18 : (segments <= (i + 1 ))) (PreH19 : (old = (Zlength (base_products)))) (PreH20 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH21 : (1 <= old)) (PreH22 : (old <= count)) (PreH23 : (count <= x_pre)) (PreH24 : (0 <= j)) (PreH25 : (j <= old)) (PreH26 : (count = (Zlength (products_before_append)))) (PreH27 : (reaches = 1)) (PreH28 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH29 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH30 : (ValuableOuterState x_pre values i segments base_products )) (PreH31 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH32 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH33 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH34 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0) ”
  &&  “ ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v )) ”
  &&  “ (j < old) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products_before_append))) ”
  &&  “ (1 <= old) ”
  &&  “ (old <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= old) ”
  &&  “ (count = (Zlength (products_before_append))) ”
  &&  “ (reaches = 1) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products j products_before_append reaches ) ”
  &&  “ (ValuableBitmap x_pre products_before_append bitmap ) ”
  &&  (((products_buf + (j * sizeof(INT)))) # Int  |-> (Znth (j - 0 ) products_before_append 0))
  **  (IntArray.missing_i products_buf j 0 count products_before_append )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
.

Definition solver_partial_solve_wit_11 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH2 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH3 : (j < old)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : (2 <= x_pre)) (PreH6 : (x_pre <= 100000)) (PreH7 : (1 <= (Zlength (values)))) (PreH8 : ((Zlength (values)) <= 100000)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH10 : (Pre x_pre values )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (v = (Znth i values 0))) (PreH14 : (1 <= v)) (PreH15 : (v <= x_pre)) (PreH16 : ((x_pre % ( v ) ) = 0)) (PreH17 : (1 <= segments)) (PreH18 : (segments <= (i + 1 ))) (PreH19 : (old = (Zlength (base_products)))) (PreH20 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH21 : (1 <= old)) (PreH22 : (old <= count)) (PreH23 : (count <= x_pre)) (PreH24 : (0 <= j)) (PreH25 : (j <= old)) (PreH26 : (count = (Zlength (products_before_append)))) (PreH27 : (reaches = 0)) (PreH28 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH29 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH30 : (ValuableOuterState x_pre values i segments base_products )) (PreH31 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH32 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH33 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH34 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0) ”
  &&  “ ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v )) ”
  &&  “ (j < old) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products_before_append))) ”
  &&  “ (1 <= old) ”
  &&  “ (old <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= old) ”
  &&  “ (count = (Zlength (products_before_append))) ”
  &&  “ (reaches = 0) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products j products_before_append reaches ) ”
  &&  “ (ValuableBitmap x_pre products_before_append bitmap ) ”
  &&  (((products_buf + (j * sizeof(INT)))) # Int  |-> (Znth (j - 0 ) products_before_append 0))
  **  (IntArray.missing_i products_buf j 0 count products_before_append )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
.

Definition solver_partial_solve_wit_12 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH2 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH3 : (reaches <= INT_MAX)) (PreH4 : (j <= INT_MAX)) (PreH5 : (count <= INT_MAX)) (PreH6 : (old <= INT_MAX)) (PreH7 : (segments <= INT_MAX)) (PreH8 : (v <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (reaches >= INT_MIN)) (PreH12 : (j >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (old >= INT_MIN)) (PreH15 : (segments >= INT_MIN)) (PreH16 : (v >= INT_MIN)) (PreH17 : (i >= INT_MIN)) (PreH18 : (n_pre >= INT_MIN)) (PreH19 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH20 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH21 : (j < old)) (PreH22 : (n_pre = (Zlength (values)))) (PreH23 : (2 <= x_pre)) (PreH24 : (x_pre <= 100000)) (PreH25 : (1 <= (Zlength (values)))) (PreH26 : ((Zlength (values)) <= 100000)) (PreH27 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH28 : (Pre x_pre values )) (PreH29 : (0 <= i)) (PreH30 : (i < n_pre)) (PreH31 : (v = (Znth i values 0))) (PreH32 : (1 <= v)) (PreH33 : (v <= x_pre)) (PreH34 : ((x_pre % ( v ) ) = 0)) (PreH35 : (1 <= segments)) (PreH36 : (segments <= (i + 1 ))) (PreH37 : (old = (Zlength (base_products)))) (PreH38 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH39 : (1 <= old)) (PreH40 : (old <= count)) (PreH41 : (count <= x_pre)) (PreH42 : (0 <= j)) (PreH43 : (j <= old)) (PreH44 : (count = (Zlength (products_before_append)))) (PreH45 : (reaches = 1)) (PreH46 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH47 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH48 : (ValuableOuterState x_pre values i segments base_products )) (PreH49 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH50 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH51 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH52 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (1 <= ((Znth (j - 0 ) products_before_append 0) * v )) ”
  &&  “ (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre) ”
  &&  “ (reaches <= INT_MAX) ”
  &&  “ (j <= INT_MAX) ”
  &&  “ (count <= INT_MAX) ”
  &&  “ (old <= INT_MAX) ”
  &&  “ (segments <= INT_MAX) ”
  &&  “ (v <= INT_MAX) ”
  &&  “ (i <= INT_MAX) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (reaches >= INT_MIN) ”
  &&  “ (j >= INT_MIN) ”
  &&  “ (count >= INT_MIN) ”
  &&  “ (old >= INT_MIN) ”
  &&  “ (segments >= INT_MIN) ”
  &&  “ (v >= INT_MIN) ”
  &&  “ (i >= INT_MIN) ”
  &&  “ (n_pre >= INT_MIN) ”
  &&  “ ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0) ”
  &&  “ ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v )) ”
  &&  “ (j < old) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products_before_append))) ”
  &&  “ (1 <= old) ”
  &&  “ (old <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= old) ”
  &&  “ (count = (Zlength (products_before_append))) ”
  &&  “ (reaches = 1) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products j products_before_append reaches ) ”
  &&  “ (ValuableBitmap x_pre products_before_append bitmap ) ”
  &&  (((used + (((Znth (j - 0 ) products_before_append 0) * v ) * sizeof(UCHAR)))) # UChar  |-> (Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap 0))
  **  (UCharArray.missing_i used ((Znth (j - 0 ) products_before_append 0) * v ) 0 (x_pre + 1 ) bitmap )
  **  (IntArray.seg products_buf 0 count products_before_append )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
.

Definition solver_partial_solve_wit_13 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH2 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH3 : (reaches <= INT_MAX)) (PreH4 : (j <= INT_MAX)) (PreH5 : (count <= INT_MAX)) (PreH6 : (old <= INT_MAX)) (PreH7 : (segments <= INT_MAX)) (PreH8 : (v <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (reaches >= INT_MIN)) (PreH12 : (j >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (old >= INT_MIN)) (PreH15 : (segments >= INT_MIN)) (PreH16 : (v >= INT_MIN)) (PreH17 : (i >= INT_MIN)) (PreH18 : (n_pre >= INT_MIN)) (PreH19 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH20 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH21 : (j < old)) (PreH22 : (n_pre = (Zlength (values)))) (PreH23 : (2 <= x_pre)) (PreH24 : (x_pre <= 100000)) (PreH25 : (1 <= (Zlength (values)))) (PreH26 : ((Zlength (values)) <= 100000)) (PreH27 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH28 : (Pre x_pre values )) (PreH29 : (0 <= i)) (PreH30 : (i < n_pre)) (PreH31 : (v = (Znth i values 0))) (PreH32 : (1 <= v)) (PreH33 : (v <= x_pre)) (PreH34 : ((x_pre % ( v ) ) = 0)) (PreH35 : (1 <= segments)) (PreH36 : (segments <= (i + 1 ))) (PreH37 : (old = (Zlength (base_products)))) (PreH38 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH39 : (1 <= old)) (PreH40 : (old <= count)) (PreH41 : (count <= x_pre)) (PreH42 : (0 <= j)) (PreH43 : (j <= old)) (PreH44 : (count = (Zlength (products_before_append)))) (PreH45 : (reaches = 0)) (PreH46 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH47 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH48 : (ValuableOuterState x_pre values i segments base_products )) (PreH49 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH50 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH51 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH52 : (ValuableBitmap x_pre products_before_append bitmap )),
  (IntArray.seg products_buf 0 count products_before_append )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (1 <= ((Znth (j - 0 ) products_before_append 0) * v )) ”
  &&  “ (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre) ”
  &&  “ (reaches <= INT_MAX) ”
  &&  “ (j <= INT_MAX) ”
  &&  “ (count <= INT_MAX) ”
  &&  “ (old <= INT_MAX) ”
  &&  “ (segments <= INT_MAX) ”
  &&  “ (v <= INT_MAX) ”
  &&  “ (i <= INT_MAX) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (reaches >= INT_MIN) ”
  &&  “ (j >= INT_MIN) ”
  &&  “ (count >= INT_MIN) ”
  &&  “ (old >= INT_MIN) ”
  &&  “ (segments >= INT_MIN) ”
  &&  “ (v >= INT_MIN) ”
  &&  “ (i >= INT_MIN) ”
  &&  “ (n_pre >= INT_MIN) ”
  &&  “ ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0) ”
  &&  “ ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v )) ”
  &&  “ (j < old) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products_before_append))) ”
  &&  “ (1 <= old) ”
  &&  “ (old <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= old) ”
  &&  “ (count = (Zlength (products_before_append))) ”
  &&  “ (reaches = 0) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products j products_before_append reaches ) ”
  &&  “ (ValuableBitmap x_pre products_before_append bitmap ) ”
  &&  (((used + (((Znth (j - 0 ) products_before_append 0) * v ) * sizeof(UCHAR)))) # UChar  |-> (Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap 0))
  **  (UCharArray.missing_i used ((Znth (j - 0 ) products_before_append 0) * v ) 0 (x_pre + 1 ) bitmap )
  **  (IntArray.seg products_buf 0 count products_before_append )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
.

Definition solver_partial_solve_wit_14 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap 0) = 0)) (PreH2 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH3 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (j <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (old <= INT_MAX)) (PreH8 : (segments <= INT_MAX)) (PreH9 : (v <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (reaches >= INT_MIN)) (PreH13 : (j >= INT_MIN)) (PreH14 : (count >= INT_MIN)) (PreH15 : (old >= INT_MIN)) (PreH16 : (segments >= INT_MIN)) (PreH17 : (v >= INT_MIN)) (PreH18 : (i >= INT_MIN)) (PreH19 : (n_pre >= INT_MIN)) (PreH20 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH21 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH22 : (j < old)) (PreH23 : (n_pre = (Zlength (values)))) (PreH24 : (2 <= x_pre)) (PreH25 : (x_pre <= 100000)) (PreH26 : (1 <= (Zlength (values)))) (PreH27 : ((Zlength (values)) <= 100000)) (PreH28 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH29 : (Pre x_pre values )) (PreH30 : (0 <= i)) (PreH31 : (i < n_pre)) (PreH32 : (v = (Znth i values 0))) (PreH33 : (1 <= v)) (PreH34 : (v <= x_pre)) (PreH35 : ((x_pre % ( v ) ) = 0)) (PreH36 : (1 <= segments)) (PreH37 : (segments <= (i + 1 ))) (PreH38 : (old = (Zlength (base_products)))) (PreH39 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH40 : (1 <= old)) (PreH41 : (old <= count)) (PreH42 : (count <= x_pre)) (PreH43 : (0 <= j)) (PreH44 : (j <= old)) (PreH45 : (count = (Zlength (products_before_append)))) (PreH46 : (reaches = 1)) (PreH47 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH48 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH49 : (ValuableOuterState x_pre values i segments base_products )) (PreH50 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH51 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH52 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH53 : (ValuableBitmap x_pre products_before_append bitmap )),
  (UCharArray.full used (x_pre + 1 ) bitmap )
  **  (IntArray.seg products_buf 0 count products_before_append )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
|--
  “ ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap 0) = 0) ”
  &&  “ (1 <= ((Znth (j - 0 ) products_before_append 0) * v )) ”
  &&  “ (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre) ”
  &&  “ (reaches <= INT_MAX) ”
  &&  “ (j <= INT_MAX) ”
  &&  “ (count <= INT_MAX) ”
  &&  “ (old <= INT_MAX) ”
  &&  “ (segments <= INT_MAX) ”
  &&  “ (v <= INT_MAX) ”
  &&  “ (i <= INT_MAX) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (reaches >= INT_MIN) ”
  &&  “ (j >= INT_MIN) ”
  &&  “ (count >= INT_MIN) ”
  &&  “ (old >= INT_MIN) ”
  &&  “ (segments >= INT_MIN) ”
  &&  “ (v >= INT_MIN) ”
  &&  “ (i >= INT_MIN) ”
  &&  “ (n_pre >= INT_MIN) ”
  &&  “ ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0) ”
  &&  “ ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v )) ”
  &&  “ (j < old) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products_before_append))) ”
  &&  “ (1 <= old) ”
  &&  “ (old <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= old) ”
  &&  “ (count = (Zlength (products_before_append))) ”
  &&  “ (reaches = 1) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products j products_before_append reaches ) ”
  &&  “ (ValuableBitmap x_pre products_before_append bitmap ) ”
  &&  (((used + (((Znth (j - 0 ) products_before_append 0) * v ) * sizeof(UCHAR)))) # UChar  |->_)
  **  (UCharArray.missing_i used ((Znth (j - 0 ) products_before_append 0) * v ) 0 (x_pre + 1 ) bitmap )
  **  (IntArray.seg products_buf 0 count products_before_append )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
.

Definition solver_partial_solve_wit_15 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap 0) = 0)) (PreH2 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH3 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (j <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (old <= INT_MAX)) (PreH8 : (segments <= INT_MAX)) (PreH9 : (v <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (reaches >= INT_MIN)) (PreH13 : (j >= INT_MIN)) (PreH14 : (count >= INT_MIN)) (PreH15 : (old >= INT_MIN)) (PreH16 : (segments >= INT_MIN)) (PreH17 : (v >= INT_MIN)) (PreH18 : (i >= INT_MIN)) (PreH19 : (n_pre >= INT_MIN)) (PreH20 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH21 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH22 : (j < old)) (PreH23 : (n_pre = (Zlength (values)))) (PreH24 : (2 <= x_pre)) (PreH25 : (x_pre <= 100000)) (PreH26 : (1 <= (Zlength (values)))) (PreH27 : ((Zlength (values)) <= 100000)) (PreH28 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH29 : (Pre x_pre values )) (PreH30 : (0 <= i)) (PreH31 : (i < n_pre)) (PreH32 : (v = (Znth i values 0))) (PreH33 : (1 <= v)) (PreH34 : (v <= x_pre)) (PreH35 : ((x_pre % ( v ) ) = 0)) (PreH36 : (1 <= segments)) (PreH37 : (segments <= (i + 1 ))) (PreH38 : (old = (Zlength (base_products)))) (PreH39 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH40 : (1 <= old)) (PreH41 : (old <= count)) (PreH42 : (count <= x_pre)) (PreH43 : (0 <= j)) (PreH44 : (j <= old)) (PreH45 : (count = (Zlength (products_before_append)))) (PreH46 : (reaches = 0)) (PreH47 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH48 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH49 : (ValuableOuterState x_pre values i segments base_products )) (PreH50 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH51 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH52 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH53 : (ValuableBitmap x_pre products_before_append bitmap )),
  (UCharArray.full used (x_pre + 1 ) bitmap )
  **  (IntArray.seg products_buf 0 count products_before_append )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
|--
  “ ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap 0) = 0) ”
  &&  “ (1 <= ((Znth (j - 0 ) products_before_append 0) * v )) ”
  &&  “ (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre) ”
  &&  “ (reaches <= INT_MAX) ”
  &&  “ (j <= INT_MAX) ”
  &&  “ (count <= INT_MAX) ”
  &&  “ (old <= INT_MAX) ”
  &&  “ (segments <= INT_MAX) ”
  &&  “ (v <= INT_MAX) ”
  &&  “ (i <= INT_MAX) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (reaches >= INT_MIN) ”
  &&  “ (j >= INT_MIN) ”
  &&  “ (count >= INT_MIN) ”
  &&  “ (old >= INT_MIN) ”
  &&  “ (segments >= INT_MIN) ”
  &&  “ (v >= INT_MIN) ”
  &&  “ (i >= INT_MIN) ”
  &&  “ (n_pre >= INT_MIN) ”
  &&  “ ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0) ”
  &&  “ ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v )) ”
  &&  “ (j < old) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products_before_append))) ”
  &&  “ (1 <= old) ”
  &&  “ (old <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= old) ”
  &&  “ (count = (Zlength (products_before_append))) ”
  &&  “ (reaches = 0) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products j products_before_append reaches ) ”
  &&  “ (ValuableBitmap x_pre products_before_append bitmap ) ”
  &&  (((used + (((Znth (j - 0 ) products_before_append 0) * v ) * sizeof(UCHAR)))) # UChar  |->_)
  **  (UCharArray.missing_i used ((Znth (j - 0 ) products_before_append 0) * v ) 0 (x_pre + 1 ) bitmap )
  **  (IntArray.seg products_buf 0 count products_before_append )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
.

Definition solver_partial_solve_wit_16 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap 0) = 0)) (PreH2 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH3 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (j <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (old <= INT_MAX)) (PreH8 : (segments <= INT_MAX)) (PreH9 : (v <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (reaches >= INT_MIN)) (PreH13 : (j >= INT_MIN)) (PreH14 : (count >= INT_MIN)) (PreH15 : (old >= INT_MIN)) (PreH16 : (segments >= INT_MIN)) (PreH17 : (v >= INT_MIN)) (PreH18 : (i >= INT_MIN)) (PreH19 : (n_pre >= INT_MIN)) (PreH20 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH21 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH22 : (j < old)) (PreH23 : (n_pre = (Zlength (values)))) (PreH24 : (2 <= x_pre)) (PreH25 : (x_pre <= 100000)) (PreH26 : (1 <= (Zlength (values)))) (PreH27 : ((Zlength (values)) <= 100000)) (PreH28 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH29 : (Pre x_pre values )) (PreH30 : (0 <= i)) (PreH31 : (i < n_pre)) (PreH32 : (v = (Znth i values 0))) (PreH33 : (1 <= v)) (PreH34 : (v <= x_pre)) (PreH35 : ((x_pre % ( v ) ) = 0)) (PreH36 : (1 <= segments)) (PreH37 : (segments <= (i + 1 ))) (PreH38 : (old = (Zlength (base_products)))) (PreH39 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH40 : (1 <= old)) (PreH41 : (old <= count)) (PreH42 : (count <= x_pre)) (PreH43 : (0 <= j)) (PreH44 : (j <= old)) (PreH45 : (count = (Zlength (products_before_append)))) (PreH46 : (reaches = 1)) (PreH47 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH48 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH49 : (ValuableOuterState x_pre values i segments base_products )) (PreH50 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH51 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH52 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH53 : (ValuableBitmap x_pre products_before_append bitmap )),
  (UCharArray.full used (x_pre + 1 ) (replace_Znth (((Znth (j - 0 ) products_before_append 0) * v )) (1) (bitmap)) )
  **  (IntArray.seg products_buf 0 count products_before_append )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
|--
  “ ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap 0) = 0) ”
  &&  “ (1 <= ((Znth (j - 0 ) products_before_append 0) * v )) ”
  &&  “ (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre) ”
  &&  “ (reaches <= INT_MAX) ”
  &&  “ (j <= INT_MAX) ”
  &&  “ (count <= INT_MAX) ”
  &&  “ (old <= INT_MAX) ”
  &&  “ (segments <= INT_MAX) ”
  &&  “ (v <= INT_MAX) ”
  &&  “ (i <= INT_MAX) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (reaches >= INT_MIN) ”
  &&  “ (j >= INT_MIN) ”
  &&  “ (count >= INT_MIN) ”
  &&  “ (old >= INT_MIN) ”
  &&  “ (segments >= INT_MIN) ”
  &&  “ (v >= INT_MIN) ”
  &&  “ (i >= INT_MIN) ”
  &&  “ (n_pre >= INT_MIN) ”
  &&  “ ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0) ”
  &&  “ ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v )) ”
  &&  “ (j < old) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products_before_append))) ”
  &&  “ (1 <= old) ”
  &&  “ (old <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= old) ”
  &&  “ (count = (Zlength (products_before_append))) ”
  &&  “ (reaches = 1) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products j products_before_append reaches ) ”
  &&  “ (ValuableBitmap x_pre products_before_append bitmap ) ”
  &&  (((products_buf + (count * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg products_buf (count + 1 ) (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) (replace_Znth (((Znth (j - 0 ) products_before_append 0) * v )) (1) (bitmap)) )
  **  (IntArray.seg products_buf 0 count products_before_append )
  **  (IntArray.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_17 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (products_before_append: (@list Z)) (PreH1 : ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap 0) = 0)) (PreH2 : (1 <= ((Znth (j - 0 ) products_before_append 0) * v ))) (PreH3 : (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre)) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (j <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (old <= INT_MAX)) (PreH8 : (segments <= INT_MAX)) (PreH9 : (v <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (reaches >= INT_MIN)) (PreH13 : (j >= INT_MIN)) (PreH14 : (count >= INT_MIN)) (PreH15 : (old >= INT_MIN)) (PreH16 : (segments >= INT_MIN)) (PreH17 : (v >= INT_MIN)) (PreH18 : (i >= INT_MIN)) (PreH19 : (n_pre >= INT_MIN)) (PreH20 : ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0)) (PreH21 : ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v ))) (PreH22 : (j < old)) (PreH23 : (n_pre = (Zlength (values)))) (PreH24 : (2 <= x_pre)) (PreH25 : (x_pre <= 100000)) (PreH26 : (1 <= (Zlength (values)))) (PreH27 : ((Zlength (values)) <= 100000)) (PreH28 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH29 : (Pre x_pre values )) (PreH30 : (0 <= i)) (PreH31 : (i < n_pre)) (PreH32 : (v = (Znth i values 0))) (PreH33 : (1 <= v)) (PreH34 : (v <= x_pre)) (PreH35 : ((x_pre % ( v ) ) = 0)) (PreH36 : (1 <= segments)) (PreH37 : (segments <= (i + 1 ))) (PreH38 : (old = (Zlength (base_products)))) (PreH39 : (base_products = (sublist (0) (old) (products_before_append)))) (PreH40 : (1 <= old)) (PreH41 : (old <= count)) (PreH42 : (count <= x_pre)) (PreH43 : (0 <= j)) (PreH44 : (j <= old)) (PreH45 : (count = (Zlength (products_before_append)))) (PreH46 : (reaches = 0)) (PreH47 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH48 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre)))) (PreH49 : (ValuableOuterState x_pre values i segments base_products )) (PreH50 : (ValuableForcedHistory x_pre values i segments base_products )) (PreH51 : (ValuableAlignedHistory x_pre values i segments base_products )) (PreH52 : (ValuableClosureState x_pre segment v base_products j products_before_append reaches )) (PreH53 : (ValuableBitmap x_pre products_before_append bitmap )),
  (UCharArray.full used (x_pre + 1 ) (replace_Znth (((Znth (j - 0 ) products_before_append 0) * v )) (1) (bitmap)) )
  **  (IntArray.seg products_buf 0 count products_before_append )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
|--
  “ ((Znth ((Znth (j - 0 ) products_before_append 0) * v ) bitmap 0) = 0) ”
  &&  “ (1 <= ((Znth (j - 0 ) products_before_append 0) * v )) ”
  &&  “ (((Znth (j - 0 ) products_before_append 0) * v ) <= x_pre) ”
  &&  “ (reaches <= INT_MAX) ”
  &&  “ (j <= INT_MAX) ”
  &&  “ (count <= INT_MAX) ”
  &&  “ (old <= INT_MAX) ”
  &&  “ (segments <= INT_MAX) ”
  &&  “ (v <= INT_MAX) ”
  &&  “ (i <= INT_MAX) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (reaches >= INT_MIN) ”
  &&  “ (j >= INT_MIN) ”
  &&  “ (count >= INT_MIN) ”
  &&  “ (old >= INT_MIN) ”
  &&  “ (segments >= INT_MIN) ”
  &&  “ (v >= INT_MIN) ”
  &&  “ (i >= INT_MIN) ”
  &&  “ (n_pre >= INT_MIN) ”
  &&  “ ((x_pre % ( ((Znth (j - 0 ) products_before_append 0) * v ) ) ) = 0) ”
  &&  “ ((Znth (j - 0 ) products_before_append 0) <= (x_pre ÷ v )) ”
  &&  “ (j < old) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (1 <= segments) ”
  &&  “ (segments <= (i + 1 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products_before_append))) ”
  &&  “ (1 <= old) ”
  &&  “ (old <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= old) ”
  &&  “ (count = (Zlength (products_before_append))) ”
  &&  “ (reaches = 0) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products_before_append 0)) /\ ((Znth k_2 products_before_append 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i segments base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i segments base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products j products_before_append reaches ) ”
  &&  “ (ValuableBitmap x_pre products_before_append bitmap ) ”
  &&  (((products_buf + (count * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg products_buf (count + 1 ) (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) (replace_Znth (((Znth (j - 0 ) products_before_append 0) * v )) (1) (bitmap)) )
  **  (IntArray.seg products_buf 0 count products_before_append )
  **  (IntArray.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_18 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (products: (@list Z)) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (PreH1 : (j < count)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (v = (Znth i values 0))) (PreH12 : (1 <= v)) (PreH13 : (v <= x_pre)) (PreH14 : ((x_pre % ( v ) ) = 0)) (PreH15 : (2 <= segments)) (PreH16 : (segments <= (i + 2 ))) (PreH17 : (old = (Zlength (base_products)))) (PreH18 : (base_products = (sublist (0) (old) (products)))) (PreH19 : (count = (Zlength (products)))) (PreH20 : (1 <= count)) (PreH21 : (count <= x_pre)) (PreH22 : (0 <= j)) (PreH23 : (j <= count)) (PreH24 : (reaches = 1)) (PreH25 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH26 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre)))) (PreH27 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH28 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH29 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH30 : (ValuableClosureState x_pre segment v base_products old products 1 )) (PreH31 : (ValuableClearingState x_pre products j bitmap )),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (j < count) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (2 <= segments) ”
  &&  “ (segments <= (i + 2 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products))) ”
  &&  “ (count = (Zlength (products))) ”
  &&  “ (1 <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= count) ”
  &&  “ (reaches = 1) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i (segments - 1 ) base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i (segments - 1 ) base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products old products 1 ) ”
  &&  “ (ValuableClearingState x_pre products j bitmap ) ”
  &&  (((products_buf + (j * sizeof(INT)))) # Int  |-> (Znth (j - 0 ) products 0))
  **  (IntArray.missing_i products_buf j 0 count products )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
.

Definition solver_partial_solve_wit_19 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (products: (@list Z)) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (PreH1 : (j < count)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (v = (Znth i values 0))) (PreH12 : (1 <= v)) (PreH13 : (v <= x_pre)) (PreH14 : ((x_pre % ( v ) ) = 0)) (PreH15 : (2 <= segments)) (PreH16 : (segments <= (i + 2 ))) (PreH17 : (old = (Zlength (base_products)))) (PreH18 : (base_products = (sublist (0) (old) (products)))) (PreH19 : (count = (Zlength (products)))) (PreH20 : (1 <= count)) (PreH21 : (count <= x_pre)) (PreH22 : (0 <= j)) (PreH23 : (j <= count)) (PreH24 : (reaches = 1)) (PreH25 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH26 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre)))) (PreH27 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH28 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH29 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH30 : (ValuableClosureState x_pre segment v base_products old products 1 )) (PreH31 : (ValuableClearingState x_pre products j bitmap )),
  (IntArray.seg products_buf 0 count products )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (j < count) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (2 <= segments) ”
  &&  “ (segments <= (i + 2 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products))) ”
  &&  “ (count = (Zlength (products))) ”
  &&  “ (1 <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= count) ”
  &&  “ (reaches = 1) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i (segments - 1 ) base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i (segments - 1 ) base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products old products 1 ) ”
  &&  “ (ValuableClearingState x_pre products j bitmap ) ”
  &&  (((used + ((Znth (j - 0 ) products 0) * sizeof(UCHAR)))) # UChar  |->_)
  **  (UCharArray.missing_i used (Znth (j - 0 ) products 0) 0 (x_pre + 1 ) bitmap )
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
.

Definition solver_partial_solve_wit_20 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (products: (@list Z)) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (PreH1 : (j >= count)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (v = (Znth i values 0))) (PreH12 : (1 <= v)) (PreH13 : (v <= x_pre)) (PreH14 : ((x_pre % ( v ) ) = 0)) (PreH15 : (2 <= segments)) (PreH16 : (segments <= (i + 2 ))) (PreH17 : (old = (Zlength (base_products)))) (PreH18 : (base_products = (sublist (0) (old) (products)))) (PreH19 : (count = (Zlength (products)))) (PreH20 : (1 <= count)) (PreH21 : (count <= x_pre)) (PreH22 : (0 <= j)) (PreH23 : (j <= count)) (PreH24 : (reaches = 1)) (PreH25 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH26 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre)))) (PreH27 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH28 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH29 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH30 : (ValuableClosureState x_pre segment v base_products old products 1 )) (PreH31 : (ValuableClearingState x_pre products j bitmap )),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (j >= count) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (2 <= segments) ”
  &&  “ (segments <= (i + 2 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products))) ”
  &&  “ (count = (Zlength (products))) ”
  &&  “ (1 <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= count) ”
  &&  “ (reaches = 1) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i (segments - 1 ) base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i (segments - 1 ) base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products old products 1 ) ”
  &&  “ (ValuableClearingState x_pre products j bitmap ) ”
  &&  (((products_buf + (0 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i products_buf 0 0 count products )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
.

Definition solver_partial_solve_wit_21 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (used: Z) (products_buf: Z) (segment: (@list Z)) (bitmap: (@list Z)) (reaches: Z) (j: Z) (count: Z) (products: (@list Z)) (base_products: (@list Z)) (old: Z) (segments: Z) (v: Z) (i: Z) (PreH1 : (j >= count)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : (2 <= x_pre)) (PreH4 : (x_pre <= 100000)) (PreH5 : (1 <= (Zlength (values)))) (PreH6 : ((Zlength (values)) <= 100000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH8 : (Pre x_pre values )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (v = (Znth i values 0))) (PreH12 : (1 <= v)) (PreH13 : (v <= x_pre)) (PreH14 : ((x_pre % ( v ) ) = 0)) (PreH15 : (2 <= segments)) (PreH16 : (segments <= (i + 2 ))) (PreH17 : (old = (Zlength (base_products)))) (PreH18 : (base_products = (sublist (0) (old) (products)))) (PreH19 : (count = (Zlength (products)))) (PreH20 : (1 <= count)) (PreH21 : (count <= x_pre)) (PreH22 : (0 <= j)) (PreH23 : (j <= count)) (PreH24 : (reaches = 1)) (PreH25 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH26 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre)))) (PreH27 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH28 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH29 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH30 : (ValuableClosureState x_pre segment v base_products old products 1 )) (PreH31 : (ValuableClearingState x_pre products j bitmap )),
  (IntArray.full products_buf count (replace_Znth (0) (1) (products)) )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (j >= count) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (2 <= segments) ”
  &&  “ (segments <= (i + 2 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (products))) ”
  &&  “ (count = (Zlength (products))) ”
  &&  “ (1 <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= count) ”
  &&  “ (reaches = 1) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < count)) -> ((1 <= (Znth k_2 products 0)) /\ ((Znth k_2 products 0) <= x_pre))) ”
  &&  “ (ValuableOuterState x_pre values i (segments - 1 ) base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i (segments - 1 ) base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products old products 1 ) ”
  &&  “ (ValuableClearingState x_pre products j bitmap ) ”
  &&  (((used + (1 * sizeof(UCHAR)))) # UChar  |->_)
  **  (UCharArray.missing_i used 1 0 (x_pre + 1 ) bitmap )
  **  (IntArray.full products_buf count (replace_Znth (0) (1) (products)) )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
.

Definition solver_partial_solve_wit_22 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (old_products: (@list Z)) (bitmap: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (products_buf: Z) (used: Z) (PreH1 : (0 <= v)) (PreH2 : (v < (x_pre + 1 ))) (PreH3 : (reaches <= INT_MAX)) (PreH4 : (count <= INT_MAX)) (PreH5 : (old <= INT_MAX)) (PreH6 : (segments <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (reaches >= INT_MIN)) (PreH10 : (count >= INT_MIN)) (PreH11 : (old >= INT_MIN)) (PreH12 : (segments >= INT_MIN)) (PreH13 : (i >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (n_pre = (Zlength (values)))) (PreH16 : (2 <= x_pre)) (PreH17 : (x_pre <= 100000)) (PreH18 : (1 <= (Zlength (values)))) (PreH19 : ((Zlength (values)) <= 100000)) (PreH20 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH21 : (Pre x_pre values )) (PreH22 : (0 <= i)) (PreH23 : (i < n_pre)) (PreH24 : (v = (Znth i values 0))) (PreH25 : (1 <= v)) (PreH26 : (v <= x_pre)) (PreH27 : ((x_pre % ( v ) ) = 0)) (PreH28 : (2 <= segments)) (PreH29 : (segments <= (i + 2 ))) (PreH30 : (old = (Zlength (base_products)))) (PreH31 : (base_products = (sublist (0) (old) (old_products)))) (PreH32 : (count = 1)) (PreH33 : (1 <= count)) (PreH34 : (count <= x_pre)) (PreH35 : (reaches = 1)) (PreH36 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH37 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH38 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH39 : (ValuableClosureState x_pre segment v base_products old old_products 1 )) (PreH40 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH41 : (ValuableBitmap x_pre (cons (1) ((@nil Z))) bitmap )),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count (cons (1) ((@nil Z))) )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (0 <= v) ”
  &&  “ (v < (x_pre + 1 )) ”
  &&  “ (reaches <= INT_MAX) ”
  &&  “ (count <= INT_MAX) ”
  &&  “ (old <= INT_MAX) ”
  &&  “ (segments <= INT_MAX) ”
  &&  “ (i <= INT_MAX) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (reaches >= INT_MIN) ”
  &&  “ (count >= INT_MIN) ”
  &&  “ (old >= INT_MIN) ”
  &&  “ (segments >= INT_MIN) ”
  &&  “ (i >= INT_MIN) ”
  &&  “ (n_pre >= INT_MIN) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (2 <= segments) ”
  &&  “ (segments <= (i + 2 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (old_products))) ”
  &&  “ (count = 1) ”
  &&  “ (1 <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (reaches = 1) ”
  &&  “ (ValuableOuterState x_pre values i (segments - 1 ) base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i (segments - 1 ) base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products old old_products 1 ) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ (ValuableBitmap x_pre (cons (1) ((@nil Z))) bitmap ) ”
  &&  (((used + (v * sizeof(UCHAR)))) # UChar  |-> (Znth v bitmap 0))
  **  (UCharArray.missing_i used v 0 (x_pre + 1 ) bitmap )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count (cons (1) ((@nil Z))) )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
.

Definition solver_partial_solve_wit_23 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (old_products: (@list Z)) (bitmap: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (products_buf: Z) (used: Z) (PreH1 : ((Znth v bitmap 0) = 0)) (PreH2 : (0 <= v)) (PreH3 : (v < (x_pre + 1 ))) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (count <= INT_MAX)) (PreH6 : (old <= INT_MAX)) (PreH7 : (segments <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (reaches >= INT_MIN)) (PreH11 : (count >= INT_MIN)) (PreH12 : (old >= INT_MIN)) (PreH13 : (segments >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (2 <= x_pre)) (PreH18 : (x_pre <= 100000)) (PreH19 : (1 <= (Zlength (values)))) (PreH20 : ((Zlength (values)) <= 100000)) (PreH21 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH22 : (Pre x_pre values )) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (v = (Znth i values 0))) (PreH26 : (1 <= v)) (PreH27 : (v <= x_pre)) (PreH28 : ((x_pre % ( v ) ) = 0)) (PreH29 : (2 <= segments)) (PreH30 : (segments <= (i + 2 ))) (PreH31 : (old = (Zlength (base_products)))) (PreH32 : (base_products = (sublist (0) (old) (old_products)))) (PreH33 : (count = 1)) (PreH34 : (1 <= count)) (PreH35 : (count <= x_pre)) (PreH36 : (reaches = 1)) (PreH37 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH38 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH39 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH40 : (ValuableClosureState x_pre segment v base_products old old_products 1 )) (PreH41 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH42 : (ValuableBitmap x_pre (cons (1) ((@nil Z))) bitmap )),
  (UCharArray.full used (x_pre + 1 ) bitmap )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count (cons (1) ((@nil Z))) )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
|--
  “ ((Znth v bitmap 0) = 0) ”
  &&  “ (0 <= v) ”
  &&  “ (v < (x_pre + 1 )) ”
  &&  “ (reaches <= INT_MAX) ”
  &&  “ (count <= INT_MAX) ”
  &&  “ (old <= INT_MAX) ”
  &&  “ (segments <= INT_MAX) ”
  &&  “ (i <= INT_MAX) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (reaches >= INT_MIN) ”
  &&  “ (count >= INT_MIN) ”
  &&  “ (old >= INT_MIN) ”
  &&  “ (segments >= INT_MIN) ”
  &&  “ (i >= INT_MIN) ”
  &&  “ (n_pre >= INT_MIN) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (2 <= segments) ”
  &&  “ (segments <= (i + 2 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (old_products))) ”
  &&  “ (count = 1) ”
  &&  “ (1 <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (reaches = 1) ”
  &&  “ (ValuableOuterState x_pre values i (segments - 1 ) base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i (segments - 1 ) base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products old old_products 1 ) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ (ValuableBitmap x_pre (cons (1) ((@nil Z))) bitmap ) ”
  &&  (((used + (v * sizeof(UCHAR)))) # UChar  |->_)
  **  (UCharArray.missing_i used v 0 (x_pre + 1 ) bitmap )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count (cons (1) ((@nil Z))) )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
.

Definition solver_partial_solve_wit_24 :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (segment: (@list Z)) (base_products: (@list Z)) (old_products: (@list Z)) (bitmap: (@list Z)) (i: Z) (v: Z) (segments: Z) (old: Z) (count: Z) (reaches: Z) (products_buf: Z) (used: Z) (PreH1 : ((Znth v bitmap 0) = 0)) (PreH2 : (0 <= v)) (PreH3 : (v < (x_pre + 1 ))) (PreH4 : (reaches <= INT_MAX)) (PreH5 : (count <= INT_MAX)) (PreH6 : (old <= INT_MAX)) (PreH7 : (segments <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (reaches >= INT_MIN)) (PreH11 : (count >= INT_MIN)) (PreH12 : (old >= INT_MIN)) (PreH13 : (segments >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (n_pre = (Zlength (values)))) (PreH17 : (2 <= x_pre)) (PreH18 : (x_pre <= 100000)) (PreH19 : (1 <= (Zlength (values)))) (PreH20 : ((Zlength (values)) <= 100000)) (PreH21 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000)))) (PreH22 : (Pre x_pre values )) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : (v = (Znth i values 0))) (PreH26 : (1 <= v)) (PreH27 : (v <= x_pre)) (PreH28 : ((x_pre % ( v ) ) = 0)) (PreH29 : (2 <= segments)) (PreH30 : (segments <= (i + 2 ))) (PreH31 : (old = (Zlength (base_products)))) (PreH32 : (base_products = (sublist (0) (old) (old_products)))) (PreH33 : (count = 1)) (PreH34 : (1 <= count)) (PreH35 : (count <= x_pre)) (PreH36 : (reaches = 1)) (PreH37 : (ValuableOuterState x_pre values i (segments - 1 ) base_products )) (PreH38 : (ValuableForcedHistory x_pre values i (segments - 1 ) base_products )) (PreH39 : (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products )) (PreH40 : (ValuableClosureState x_pre segment v base_products old old_products 1 )) (PreH41 : ((Zlength (bitmap)) = (x_pre + 1 ))) (PreH42 : (ValuableBitmap x_pre (cons (1) ((@nil Z))) bitmap )),
  (UCharArray.full used (x_pre + 1 ) (replace_Znth (v) (1) (bitmap)) )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count (cons (1) ((@nil Z))) )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
|--
  “ ((Znth v bitmap 0) = 0) ”
  &&  “ (0 <= v) ”
  &&  “ (v < (x_pre + 1 )) ”
  &&  “ (reaches <= INT_MAX) ”
  &&  “ (count <= INT_MAX) ”
  &&  “ (old <= INT_MAX) ”
  &&  “ (segments <= INT_MAX) ”
  &&  “ (i <= INT_MAX) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (reaches >= INT_MIN) ”
  &&  “ (count >= INT_MIN) ”
  &&  “ (old >= INT_MIN) ”
  &&  “ (segments >= INT_MIN) ”
  &&  “ (i >= INT_MIN) ”
  &&  “ (n_pre >= INT_MIN) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (2 <= x_pre) ”
  &&  “ (x_pre <= 100000) ”
  &&  “ (1 <= (Zlength (values))) ”
  &&  “ ((Zlength (values)) <= 100000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (values)))) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 200000))) ”
  &&  “ (Pre x_pre values ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (v = (Znth i values 0)) ”
  &&  “ (1 <= v) ”
  &&  “ (v <= x_pre) ”
  &&  “ ((x_pre % ( v ) ) = 0) ”
  &&  “ (2 <= segments) ”
  &&  “ (segments <= (i + 2 )) ”
  &&  “ (old = (Zlength (base_products))) ”
  &&  “ (base_products = (sublist (0) (old) (old_products))) ”
  &&  “ (count = 1) ”
  &&  “ (1 <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ (reaches = 1) ”
  &&  “ (ValuableOuterState x_pre values i (segments - 1 ) base_products ) ”
  &&  “ (ValuableForcedHistory x_pre values i (segments - 1 ) base_products ) ”
  &&  “ (ValuableAlignedHistory x_pre values i (segments - 1 ) base_products ) ”
  &&  “ (ValuableClosureState x_pre segment v base_products old old_products 1 ) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ (ValuableBitmap x_pre (cons (1) ((@nil Z))) bitmap ) ”
  &&  (((products_buf + (count * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg products_buf (count + 1 ) (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) (replace_Znth (v) (1) (bitmap)) )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count (cons (1) ((@nil Z))) )
.

Definition solver_partial_solve_wit_25_pure :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (products: (@list Z)) (bitmap: (@list Z)) (segments: Z) (count: Z) (products_buf: Z) (used: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (Spec x_pre values segments )) (PreH3 : (ValuableAlignedHistory x_pre values n_pre segments products )) (PreH4 : (count = (Zlength (products)))) (PreH5 : (1 <= count)) (PreH6 : (count <= x_pre)) (PreH7 : ((Zlength (bitmap)) = (x_pre + 1 ))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (0 <= (x_pre + 1 )) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
.

Definition solver_partial_solve_wit_25_aux :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (products: (@list Z)) (bitmap: (@list Z)) (segments: Z) (count: Z) (products_buf: Z) (used: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (Spec x_pre values segments )) (PreH3 : (ValuableAlignedHistory x_pre values n_pre segments products )) (PreH4 : (count = (Zlength (products)))) (PreH5 : (1 <= count)) (PreH6 : (count <= x_pre)) (PreH7 : ((Zlength (bitmap)) = (x_pre + 1 ))),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (UCharArray.full used (x_pre + 1 ) bitmap )
|--
  “ (0 <= (x_pre + 1 )) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (Spec x_pre values segments ) ”
  &&  “ (ValuableAlignedHistory x_pre values n_pre segments products ) ”
  &&  “ (count = (Zlength (products))) ”
  &&  “ (1 <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  (UCharArray.full used (x_pre + 1 ) bitmap )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
.

Definition solver_partial_solve_wit_25 := solver_partial_solve_wit_25_pure -> solver_partial_solve_wit_25_aux.

Definition solver_partial_solve_wit_26_pure :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (products: (@list Z)) (bitmap: (@list Z)) (segments: Z) (count: Z) (products_buf: Z) (used: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (Spec x_pre values segments )) (PreH3 : (ValuableAlignedHistory x_pre values n_pre segments products )) (PreH4 : (count = (Zlength (products)))) (PreH5 : (1 <= count)) (PreH6 : (count <= x_pre)) (PreH7 : ((Zlength (bitmap)) = (x_pre + 1 ))),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "products_buf" ) )) # Ptr  |-> products_buf)
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  ((( &( "used" ) )) # Ptr  |-> used)
|--
  “ (0 <= count) ”
  &&  “ (count <= (x_pre + 1 )) ”
  &&  “ ((Zlength (products)) = count) ”
.

Definition solver_partial_solve_wit_26_aux :=
forall (values: (@list Z)) (a_pre: Z) (n_pre: Z) (x_pre: Z) (products: (@list Z)) (bitmap: (@list Z)) (segments: Z) (count: Z) (products_buf: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : (Spec x_pre values segments )) (PreH3 : (ValuableAlignedHistory x_pre values n_pre segments products )) (PreH4 : (count = (Zlength (products)))) (PreH5 : (1 <= count)) (PreH6 : (count <= x_pre)) (PreH7 : ((Zlength (bitmap)) = (x_pre + 1 ))),
  (IntArray.full a_pre n_pre values )
  **  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
|--
  “ (0 <= count) ”
  &&  “ (count <= (x_pre + 1 )) ”
  &&  “ ((Zlength (products)) = count) ”
  &&  “ (n_pre = (Zlength (values))) ”
  &&  “ (Spec x_pre values segments ) ”
  &&  “ (ValuableAlignedHistory x_pre values n_pre segments products ) ”
  &&  “ (count = (Zlength (products))) ”
  &&  “ (1 <= count) ”
  &&  “ (count <= x_pre) ”
  &&  “ ((Zlength (bitmap)) = (x_pre + 1 )) ”
  &&  (IntArray.seg products_buf 0 count products )
  **  (IntArray.undef_seg products_buf count (x_pre + 1 ) )
  **  (IntArray.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_26 := solver_partial_solve_wit_26_pure -> solver_partial_solve_wit_26_aux.

Module Type VC_Correct.

Include string_Strategy_Correct.

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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1.
Axiom proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2.
Axiom proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Axiom proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Axiom proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Axiom proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Axiom proof_of_solver_entail_wit_6_1 : solver_entail_wit_6_1.
Axiom proof_of_solver_entail_wit_6_2 : solver_entail_wit_6_2.
Axiom proof_of_solver_entail_wit_6_3 : solver_entail_wit_6_3.
Axiom proof_of_solver_entail_wit_6_4 : solver_entail_wit_6_4.
Axiom proof_of_solver_entail_wit_6_5 : solver_entail_wit_6_5.
Axiom proof_of_solver_entail_wit_6_6 : solver_entail_wit_6_6.
Axiom proof_of_solver_entail_wit_6_7 : solver_entail_wit_6_7.
Axiom proof_of_solver_entail_wit_6_8 : solver_entail_wit_6_8.
Axiom proof_of_solver_entail_wit_6_9 : solver_entail_wit_6_9.
Axiom proof_of_solver_entail_wit_6_10 : solver_entail_wit_6_10.
Axiom proof_of_solver_entail_wit_6_11 : solver_entail_wit_6_11.
Axiom proof_of_solver_entail_wit_6_12 : solver_entail_wit_6_12.
Axiom proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Axiom proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Axiom proof_of_solver_entail_wit_8_1 : solver_entail_wit_8_1.
Axiom proof_of_solver_entail_wit_8_2 : solver_entail_wit_8_2.
Axiom proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Axiom proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Axiom proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Axiom proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Axiom proof_of_solver_entail_wit_13 : solver_entail_wit_13.
Axiom proof_of_solver_entail_wit_14_1 : solver_entail_wit_14_1.
Axiom proof_of_solver_entail_wit_14_2 : solver_entail_wit_14_2.
Axiom proof_of_solver_entail_wit_14_3 : solver_entail_wit_14_3.
Axiom proof_of_solver_entail_wit_14_4 : solver_entail_wit_14_4.
Axiom proof_of_solver_entail_wit_15 : solver_entail_wit_15.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
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
Axiom proof_of_solver_partial_solve_wit_25_pure : solver_partial_solve_wit_25_pure.
Axiom proof_of_solver_partial_solve_wit_25 : solver_partial_solve_wit_25.
Axiom proof_of_solver_partial_solve_wit_26_pure : solver_partial_solve_wit_26_pure.
Axiom proof_of_solver_partial_solve_wit_26 : solver_partial_solve_wit_26.

End VC_Correct.
