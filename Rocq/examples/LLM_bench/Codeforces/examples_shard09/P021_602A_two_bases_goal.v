From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P021_602A_two_bases_lib.
Local Open Scope sac.

(*----- Function numeral_value -----*)

Definition numeral_value_safety_wit_1 :=
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10)) (PreH3 : (2 <= b_pre)) (PreH4 : (b_pre <= 40)) (PreH5 : (n_pre = (Zlength (digits)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k digits 0)) /\ ((Znth k digits 0) < b_pre)))),
  ((( &( "v" ) )) # Int64  |->_)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  (IntArray.full d_pre n_pre digits )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition numeral_value_safety_wit_2 :=
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10)) (PreH3 : (2 <= b_pre)) (PreH4 : (b_pre <= 40)) (PreH5 : (n_pre = (Zlength (digits)))) (PreH6 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k digits 0)) /\ ((Znth k digits 0) < b_pre)))),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Int64  |-> 0)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  (IntArray.full d_pre n_pre digits )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition numeral_value_safety_wit_3 :=
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (b_pre: Z) (v: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (2 <= b_pre)) (PreH5 : (b_pre <= 40)) (PreH6 : (n_pre = (Zlength (digits)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k digits 0)) /\ ((Znth k digits 0) < b_pre)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (v = (numeral (b_pre) ((sublist (0) (i) (digits)))))) (PreH11 : (0 <= v)) (PreH12 : (v <= ((Z.pow (40) (i)) - 1 ))),
  (IntArray.full d_pre n_pre digits )
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> ((v * b_pre ) + (Znth i digits 0) ))
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition numeral_value_safety_wit_4 :=
(
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (b_pre: Z) (v: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (2 <= b_pre)) (PreH5 : (b_pre <= 40)) (PreH6 : (n_pre = (Zlength (digits)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k digits 0)) /\ ((Znth k digits 0) < b_pre)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (v = (numeral (b_pre) ((sublist (0) (i) (digits)))))) (PreH11 : (0 <= v)) (PreH12 : (v <= ((Z.pow (40) (i)) - 1 ))),
  (IntArray.full d_pre n_pre digits )
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
|--
  “ (((v * b_pre ) + (Znth i digits 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((v * b_pre ) + (Znth i digits 0) )) ”
) \/
(
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (b_pre: Z) (v: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (2 <= b_pre)) (PreH5 : (b_pre <= 40)) (PreH6 : (n_pre = (Zlength (digits)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k digits 0)) /\ ((Znth k digits 0) < b_pre)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (v = (numeral (b_pre) ((sublist (0) (i) (digits)))))) (PreH11 : (0 <= v)) (PreH12 : (v <= ((Z.pow (40) (i)) - 1 ))),
  (IntArray.full d_pre n_pre digits )
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
|--
  “ (((v * b_pre ) + (Znth i digits 0) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((v * b_pre ) + (Znth i digits 0) )) ”
).

Definition numeral_value_safety_wit_4_split_goal_1 :=
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (b_pre: Z) (v: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (2 <= b_pre)) (PreH5 : (b_pre <= 40)) (PreH6 : (n_pre = (Zlength (digits)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k digits 0)) /\ ((Znth k digits 0) < b_pre)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (v = (numeral (b_pre) ((sublist (0) (i) (digits)))))) (PreH11 : (0 <= v)) (PreH12 : (v <= ((Z.pow (40) (i)) - 1 ))),
  (IntArray.full d_pre n_pre digits )
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
|--
  “ (((v * b_pre ) + (Znth i digits 0) ) <= INT64_MAX) ”
.

Definition numeral_value_safety_wit_4_split_goal_2 :=
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (b_pre: Z) (v: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (2 <= b_pre)) (PreH5 : (b_pre <= 40)) (PreH6 : (n_pre = (Zlength (digits)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k digits 0)) /\ ((Znth k digits 0) < b_pre)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (v = (numeral (b_pre) ((sublist (0) (i) (digits)))))) (PreH11 : (0 <= v)) (PreH12 : (v <= ((Z.pow (40) (i)) - 1 ))),
  (IntArray.full d_pre n_pre digits )
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
|--
  “ ((INT64_MIN) <= ((v * b_pre ) + (Znth i digits 0) )) ”
.

Definition numeral_value_safety_wit_5 :=
(
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (b_pre: Z) (v: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (2 <= b_pre)) (PreH5 : (b_pre <= 40)) (PreH6 : (n_pre = (Zlength (digits)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k digits 0)) /\ ((Znth k digits 0) < b_pre)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (v = (numeral (b_pre) ((sublist (0) (i) (digits)))))) (PreH11 : (0 <= v)) (PreH12 : (v <= ((Z.pow (40) (i)) - 1 ))),
  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  (IntArray.full d_pre n_pre digits )
|--
  “ ((v * b_pre ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (v * b_pre )) ”
) \/
(
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (b_pre: Z) (v: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (2 <= b_pre)) (PreH5 : (b_pre <= 40)) (PreH6 : (n_pre = (Zlength (digits)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k digits 0)) /\ ((Znth k digits 0) < b_pre)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (v = (numeral (b_pre) ((sublist (0) (i) (digits)))))) (PreH11 : (0 <= v)) (PreH12 : (v <= ((Z.pow (40) (i)) - 1 ))),
  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  (IntArray.full d_pre n_pre digits )
|--
  “ ((v * b_pre ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (v * b_pre )) ”
).

Definition numeral_value_safety_wit_5_split_goal_1 :=
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (b_pre: Z) (v: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (2 <= b_pre)) (PreH5 : (b_pre <= 40)) (PreH6 : (n_pre = (Zlength (digits)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k digits 0)) /\ ((Znth k digits 0) < b_pre)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (v = (numeral (b_pre) ((sublist (0) (i) (digits)))))) (PreH11 : (0 <= v)) (PreH12 : (v <= ((Z.pow (40) (i)) - 1 ))),
  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  (IntArray.full d_pre n_pre digits )
|--
  “ ((v * b_pre ) <= INT64_MAX) ”
.

Definition numeral_value_safety_wit_5_split_goal_2 :=
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (b_pre: Z) (v: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (2 <= b_pre)) (PreH5 : (b_pre <= 40)) (PreH6 : (n_pre = (Zlength (digits)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k digits 0)) /\ ((Znth k digits 0) < b_pre)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (v = (numeral (b_pre) ((sublist (0) (i) (digits)))))) (PreH11 : (0 <= v)) (PreH12 : (v <= ((Z.pow (40) (i)) - 1 ))),
  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "v" ) )) # Int64  |-> v)
  **  (IntArray.full d_pre n_pre digits )
|--
  “ ((INT64_MIN) <= (v * b_pre )) ”
.

Definition numeral_value_entail_wit_1 :=
(
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (b_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10)) (PreH3 : (2 <= b_pre)) (PreH4 : (b_pre <= 40)) (PreH5 : (n_pre = (Zlength (digits)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 digits 0)) /\ ((Znth k_2 digits 0) < b_pre)))),
  (IntArray.full d_pre n_pre digits )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 10) ”
  &&  “ (2 <= b_pre) ”
  &&  “ (b_pre <= 40) ”
  &&  “ (n_pre = (Zlength (digits))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k digits 0)) /\ ((Znth k digits 0) < b_pre))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (0 = (numeral (b_pre) ((sublist (0) (0) (digits))))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= ((Z.pow (40) (0)) - 1 )) ”
  &&  (IntArray.full d_pre n_pre digits )
) \/
(
forall (digits: (@list Z)) (n_pre: Z) (b_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10)) (PreH3 : (2 <= b_pre)) (PreH4 : (b_pre <= 40)) (PreH5 : (n_pre = (Zlength (digits)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 digits 0)) /\ ((Znth k_2 digits 0) < b_pre)))),
  TT && emp 
|--
  “ (0 <= ((Z.pow (40) (0)) - 1 )) ”
  &&  “ (0 = (numeral (b_pre) ((sublist (0) (0) (digits))))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k digits 0)) /\ ((Znth k digits 0) < b_pre))) ”
  &&  emp
).

Definition numeral_value_entail_wit_1_split_goal_1 :=
forall (digits: (@list Z)) (n_pre: Z) (b_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10)) (PreH3 : (2 <= b_pre)) (PreH4 : (b_pre <= 40)) (PreH5 : (n_pre = (Zlength (digits)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 digits 0)) /\ ((Znth k_2 digits 0) < b_pre)))),
  (0 <= ((Z.pow (40) (0)) - 1 ))
.

Definition numeral_value_entail_wit_1_split_goal_2 :=
forall (digits: (@list Z)) (n_pre: Z) (b_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10)) (PreH3 : (2 <= b_pre)) (PreH4 : (b_pre <= 40)) (PreH5 : (n_pre = (Zlength (digits)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 digits 0)) /\ ((Znth k_2 digits 0) < b_pre)))),
  (0 = (numeral (b_pre) ((sublist (0) (0) (digits)))))
.

Definition numeral_value_entail_wit_1_split_goal_3 :=
forall (digits: (@list Z)) (n_pre: Z) (b_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10)) (PreH3 : (2 <= b_pre)) (PreH4 : (b_pre <= 40)) (PreH5 : (n_pre = (Zlength (digits)))) (PreH6 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 digits 0)) /\ ((Znth k_2 digits 0) < b_pre)))),
  forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k digits 0)) /\ ((Znth k digits 0) < b_pre)))
.

Definition numeral_value_entail_wit_2 :=
(
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (b_pre: Z) (v: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (2 <= b_pre)) (PreH5 : (b_pre <= 40)) (PreH6 : (n_pre = (Zlength (digits)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k digits 0)) /\ ((Znth k digits 0) < b_pre)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (v = (numeral (b_pre) ((sublist (0) (i) (digits)))))) (PreH11 : (0 <= v)) (PreH12 : (v <= ((Z.pow (40) (i)) - 1 ))),
  (IntArray.full d_pre n_pre digits )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 10) ”
  &&  “ (2 <= b_pre) ”
  &&  “ (b_pre <= 40) ”
  &&  “ (n_pre = (Zlength (digits))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k digits 0)) /\ ((Znth k digits 0) < b_pre))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (((v * b_pre ) + (Znth i digits 0) ) = (numeral (b_pre) ((sublist (0) ((i + 1 )) (digits))))) ”
  &&  “ (0 <= ((v * b_pre ) + (Znth i digits 0) )) ”
  &&  “ (((v * b_pre ) + (Znth i digits 0) ) <= ((Z.pow (40) ((i + 1 ))) - 1 )) ”
  &&  (IntArray.full d_pre n_pre digits )
) \/
(
forall (digits: (@list Z)) (n_pre: Z) (b_pre: Z) (v: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (2 <= b_pre)) (PreH5 : (b_pre <= 40)) (PreH6 : (n_pre = (Zlength (digits)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k digits 0)) /\ ((Znth k digits 0) < b_pre)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (v = (numeral (b_pre) ((sublist (0) (i) (digits)))))) (PreH11 : (0 <= v)) (PreH12 : (v <= ((Z.pow (40) (i)) - 1 ))),
  TT && emp 
|--
  “ (((v * b_pre ) + (Znth i digits 0) ) <= ((Z.pow (40) ((i + 1 ))) - 1 )) ”
  &&  “ (((v * b_pre ) + (Znth i digits 0) ) = (numeral (b_pre) ((sublist (0) ((i + 1 )) (digits))))) ”
  &&  emp
).

Definition numeral_value_entail_wit_2_split_goal_1 :=
forall (digits: (@list Z)) (n_pre: Z) (b_pre: Z) (v: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (2 <= b_pre)) (PreH5 : (b_pre <= 40)) (PreH6 : (n_pre = (Zlength (digits)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k digits 0)) /\ ((Znth k digits 0) < b_pre)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (v = (numeral (b_pre) ((sublist (0) (i) (digits)))))) (PreH11 : (0 <= v)) (PreH12 : (v <= ((Z.pow (40) (i)) - 1 ))),
  (((v * b_pre ) + (Znth i digits 0) ) <= ((Z.pow (40) ((i + 1 ))) - 1 ))
.

Definition numeral_value_entail_wit_2_split_goal_2 :=
forall (digits: (@list Z)) (n_pre: Z) (b_pre: Z) (v: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (2 <= b_pre)) (PreH5 : (b_pre <= 40)) (PreH6 : (n_pre = (Zlength (digits)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k digits 0)) /\ ((Znth k digits 0) < b_pre)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (v = (numeral (b_pre) ((sublist (0) (i) (digits)))))) (PreH11 : (0 <= v)) (PreH12 : (v <= ((Z.pow (40) (i)) - 1 ))),
  (((v * b_pre ) + (Znth i digits 0) ) = (numeral (b_pre) ((sublist (0) ((i + 1 )) (digits)))))
.

Definition numeral_value_return_wit_1 :=
(
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (b_pre: Z) (v: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (2 <= b_pre)) (PreH5 : (b_pre <= 40)) (PreH6 : (n_pre = (Zlength (digits)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k digits 0)) /\ ((Znth k digits 0) < b_pre)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (v = (numeral (b_pre) ((sublist (0) (i) (digits)))))) (PreH11 : (0 <= v)) (PreH12 : (v <= ((Z.pow (40) (i)) - 1 ))),
  (IntArray.full d_pre n_pre digits )
|--
  “ (v = (numeral (b_pre) (digits))) ”
  &&  (IntArray.full d_pre n_pre digits )
) \/
(
forall (digits: (@list Z)) (n_pre: Z) (b_pre: Z) (v: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (2 <= b_pre)) (PreH5 : (b_pre <= 40)) (PreH6 : (n_pre = (Zlength (digits)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k digits 0)) /\ ((Znth k digits 0) < b_pre)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (v = (numeral (b_pre) ((sublist (0) (i) (digits)))))) (PreH11 : (0 <= v)) (PreH12 : (v <= ((Z.pow (40) (i)) - 1 ))),
  TT && emp 
|--
  “ (v = (numeral (b_pre) (digits))) ”
  &&  emp
).

Definition numeral_value_return_wit_1_split_goal_1 :=
forall (digits: (@list Z)) (n_pre: Z) (b_pre: Z) (v: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (2 <= b_pre)) (PreH5 : (b_pre <= 40)) (PreH6 : (n_pre = (Zlength (digits)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k digits 0)) /\ ((Znth k digits 0) < b_pre)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (v = (numeral (b_pre) ((sublist (0) (i) (digits)))))) (PreH11 : (0 <= v)) (PreH12 : (v <= ((Z.pow (40) (i)) - 1 ))),
  (v = (numeral (b_pre) (digits)))
.

Definition numeral_value_partial_solve_wit_1 :=
forall (digits: (@list Z)) (d_pre: Z) (n_pre: Z) (b_pre: Z) (v: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (2 <= b_pre)) (PreH5 : (b_pre <= 40)) (PreH6 : (n_pre = (Zlength (digits)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k digits 0)) /\ ((Znth k digits 0) < b_pre)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (v = (numeral (b_pre) ((sublist (0) (i) (digits)))))) (PreH11 : (0 <= v)) (PreH12 : (v <= ((Z.pow (40) (i)) - 1 ))),
  (IntArray.full d_pre n_pre digits )
|--
  “ (i < n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 10) ”
  &&  “ (2 <= b_pre) ”
  &&  “ (b_pre <= 40) ”
  &&  “ (n_pre = (Zlength (digits))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k digits 0)) /\ ((Znth k digits 0) < b_pre))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (v = (numeral (b_pre) ((sublist (0) (i) (digits))))) ”
  &&  “ (0 <= v) ”
  &&  “ (v <= ((Z.pow (40) (i)) - 1 )) ”
  &&  (((d_pre + (i * sizeof(INT)))) # Int  |-> (Znth i digits 0))
  **  (IntArray.missing_i d_pre i 0 n_pre digits )
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (y_digits: (@list Z)) (x_digits: (@list Z)) (bx_pre: Z) (basey_pre: Z) (x_pre: Z) (n_pre: Z) (y_pre: Z) (m_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval < retval_2)) (PreH2 : (retval_2 = (numeral (basey_pre) (y_digits)))) (PreH3 : (retval = (numeral (bx_pre) (x_digits)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 10)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 10)) (PreH8 : (2 <= bx_pre)) (PreH9 : (bx_pre <= 40)) (PreH10 : (2 <= basey_pre)) (PreH11 : (basey_pre <= 40)) (PreH12 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i x_digits 0)) /\ ((Znth i x_digits 0) < bx_pre)))) (PreH13 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> ((0 <= (Znth i_2 y_digits 0)) /\ ((Znth i_2 y_digits 0) < basey_pre)))) (PreH14 : (Pre bx_pre basey_pre x_digits y_digits )) (PreH15 : (n_pre = (Zlength (x_digits)))) (PreH16 : (m_pre = (Zlength (y_digits)))),
  (IntArray.full y_pre m_pre y_digits )
  **  ((( &( "vy" ) )) # Int64  |-> retval_2)
  **  (IntArray.full x_pre n_pre x_digits )
  **  ((( &( "vx" ) )) # Int64  |-> retval)
  **  ((( &( "bx" ) )) # Int  |-> bx_pre)
  **  ((( &( "basey" ) )) # Int  |-> basey_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
|--
  “ (60 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 60) ”
.

Definition solver_safety_wit_2 :=
forall (y_digits: (@list Z)) (x_digits: (@list Z)) (bx_pre: Z) (basey_pre: Z) (x_pre: Z) (n_pre: Z) (y_pre: Z) (m_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval > retval_2)) (PreH2 : (retval >= retval_2)) (PreH3 : (retval_2 = (numeral (basey_pre) (y_digits)))) (PreH4 : (retval = (numeral (bx_pre) (x_digits)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 10)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 10)) (PreH9 : (2 <= bx_pre)) (PreH10 : (bx_pre <= 40)) (PreH11 : (2 <= basey_pre)) (PreH12 : (basey_pre <= 40)) (PreH13 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i x_digits 0)) /\ ((Znth i x_digits 0) < bx_pre)))) (PreH14 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> ((0 <= (Znth i_2 y_digits 0)) /\ ((Znth i_2 y_digits 0) < basey_pre)))) (PreH15 : (Pre bx_pre basey_pre x_digits y_digits )) (PreH16 : (n_pre = (Zlength (x_digits)))) (PreH17 : (m_pre = (Zlength (y_digits)))),
  (IntArray.full y_pre m_pre y_digits )
  **  ((( &( "vy" ) )) # Int64  |-> retval_2)
  **  (IntArray.full x_pre n_pre x_digits )
  **  ((( &( "vx" ) )) # Int64  |-> retval)
  **  ((( &( "bx" ) )) # Int  |-> bx_pre)
  **  ((( &( "basey" ) )) # Int  |-> basey_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
|--
  “ (62 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 62) ”
.

Definition solver_safety_wit_3 :=
forall (y_digits: (@list Z)) (x_digits: (@list Z)) (bx_pre: Z) (basey_pre: Z) (x_pre: Z) (n_pre: Z) (y_pre: Z) (m_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval <= retval_2)) (PreH2 : (retval >= retval_2)) (PreH3 : (retval_2 = (numeral (basey_pre) (y_digits)))) (PreH4 : (retval = (numeral (bx_pre) (x_digits)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 10)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 10)) (PreH9 : (2 <= bx_pre)) (PreH10 : (bx_pre <= 40)) (PreH11 : (2 <= basey_pre)) (PreH12 : (basey_pre <= 40)) (PreH13 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i x_digits 0)) /\ ((Znth i x_digits 0) < bx_pre)))) (PreH14 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> ((0 <= (Znth i_2 y_digits 0)) /\ ((Znth i_2 y_digits 0) < basey_pre)))) (PreH15 : (Pre bx_pre basey_pre x_digits y_digits )) (PreH16 : (n_pre = (Zlength (x_digits)))) (PreH17 : (m_pre = (Zlength (y_digits)))),
  (IntArray.full y_pre m_pre y_digits )
  **  ((( &( "vy" ) )) # Int64  |-> retval_2)
  **  (IntArray.full x_pre n_pre x_digits )
  **  ((( &( "vx" ) )) # Int64  |-> retval)
  **  ((( &( "bx" ) )) # Int  |-> bx_pre)
  **  ((( &( "basey" ) )) # Int  |-> basey_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
|--
  “ (61 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 61) ”
.

Definition solver_return_wit_1 :=
(
forall (y_digits: (@list Z)) (x_digits: (@list Z)) (bx_pre: Z) (basey_pre: Z) (x_pre: Z) (n_pre: Z) (y_pre: Z) (m_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval < retval_2)) (PreH2 : (retval_2 = (numeral (basey_pre) (y_digits)))) (PreH3 : (retval = (numeral (bx_pre) (x_digits)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 10)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 10)) (PreH8 : (2 <= bx_pre)) (PreH9 : (bx_pre <= 40)) (PreH10 : (2 <= basey_pre)) (PreH11 : (basey_pre <= 40)) (PreH12 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i x_digits 0)) /\ ((Znth i x_digits 0) < bx_pre)))) (PreH13 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> ((0 <= (Znth i_2 y_digits 0)) /\ ((Znth i_2 y_digits 0) < basey_pre)))) (PreH14 : (Pre bx_pre basey_pre x_digits y_digits )) (PreH15 : (n_pre = (Zlength (x_digits)))) (PreH16 : (m_pre = (Zlength (y_digits)))),
  (IntArray.full y_pre m_pre y_digits )
  **  (IntArray.full x_pre n_pre x_digits )
|--
  “ (Spec bx_pre basey_pre x_digits y_digits 60 ) ”
  &&  (IntArray.full x_pre n_pre x_digits )
  **  (IntArray.full y_pre m_pre y_digits )
) \/
(
forall (y_digits: (@list Z)) (x_digits: (@list Z)) (bx_pre: Z) (basey_pre: Z) (n_pre: Z) (m_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval < retval_2)) (PreH2 : (retval_2 = (numeral (basey_pre) (y_digits)))) (PreH3 : (retval = (numeral (bx_pre) (x_digits)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 10)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 10)) (PreH8 : (2 <= bx_pre)) (PreH9 : (bx_pre <= 40)) (PreH10 : (2 <= basey_pre)) (PreH11 : (basey_pre <= 40)) (PreH12 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i x_digits 0)) /\ ((Znth i x_digits 0) < bx_pre)))) (PreH13 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> ((0 <= (Znth i_2 y_digits 0)) /\ ((Znth i_2 y_digits 0) < basey_pre)))) (PreH14 : (Pre bx_pre basey_pre x_digits y_digits )) (PreH15 : (n_pre = (Zlength (x_digits)))) (PreH16 : (m_pre = (Zlength (y_digits)))),
  TT && emp 
|--
  “ (Spec bx_pre basey_pre x_digits y_digits 60 ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (y_digits: (@list Z)) (x_digits: (@list Z)) (bx_pre: Z) (basey_pre: Z) (n_pre: Z) (m_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval < retval_2)) (PreH2 : (retval_2 = (numeral (basey_pre) (y_digits)))) (PreH3 : (retval = (numeral (bx_pre) (x_digits)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 10)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 10)) (PreH8 : (2 <= bx_pre)) (PreH9 : (bx_pre <= 40)) (PreH10 : (2 <= basey_pre)) (PreH11 : (basey_pre <= 40)) (PreH12 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i x_digits 0)) /\ ((Znth i x_digits 0) < bx_pre)))) (PreH13 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> ((0 <= (Znth i_2 y_digits 0)) /\ ((Znth i_2 y_digits 0) < basey_pre)))) (PreH14 : (Pre bx_pre basey_pre x_digits y_digits )) (PreH15 : (n_pre = (Zlength (x_digits)))) (PreH16 : (m_pre = (Zlength (y_digits)))),
  (Spec bx_pre basey_pre x_digits y_digits 60 )
.

Definition solver_return_wit_2 :=
(
forall (y_digits: (@list Z)) (x_digits: (@list Z)) (bx_pre: Z) (basey_pre: Z) (x_pre: Z) (n_pre: Z) (y_pre: Z) (m_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval > retval_2)) (PreH2 : (retval >= retval_2)) (PreH3 : (retval_2 = (numeral (basey_pre) (y_digits)))) (PreH4 : (retval = (numeral (bx_pre) (x_digits)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 10)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 10)) (PreH9 : (2 <= bx_pre)) (PreH10 : (bx_pre <= 40)) (PreH11 : (2 <= basey_pre)) (PreH12 : (basey_pre <= 40)) (PreH13 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i x_digits 0)) /\ ((Znth i x_digits 0) < bx_pre)))) (PreH14 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> ((0 <= (Znth i_2 y_digits 0)) /\ ((Znth i_2 y_digits 0) < basey_pre)))) (PreH15 : (Pre bx_pre basey_pre x_digits y_digits )) (PreH16 : (n_pre = (Zlength (x_digits)))) (PreH17 : (m_pre = (Zlength (y_digits)))),
  (IntArray.full y_pre m_pre y_digits )
  **  (IntArray.full x_pre n_pre x_digits )
|--
  “ (Spec bx_pre basey_pre x_digits y_digits 62 ) ”
  &&  (IntArray.full x_pre n_pre x_digits )
  **  (IntArray.full y_pre m_pre y_digits )
) \/
(
forall (y_digits: (@list Z)) (x_digits: (@list Z)) (bx_pre: Z) (basey_pre: Z) (n_pre: Z) (m_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval > retval_2)) (PreH2 : (retval >= retval_2)) (PreH3 : (retval_2 = (numeral (basey_pre) (y_digits)))) (PreH4 : (retval = (numeral (bx_pre) (x_digits)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 10)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 10)) (PreH9 : (2 <= bx_pre)) (PreH10 : (bx_pre <= 40)) (PreH11 : (2 <= basey_pre)) (PreH12 : (basey_pre <= 40)) (PreH13 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i x_digits 0)) /\ ((Znth i x_digits 0) < bx_pre)))) (PreH14 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> ((0 <= (Znth i_2 y_digits 0)) /\ ((Znth i_2 y_digits 0) < basey_pre)))) (PreH15 : (Pre bx_pre basey_pre x_digits y_digits )) (PreH16 : (n_pre = (Zlength (x_digits)))) (PreH17 : (m_pre = (Zlength (y_digits)))),
  TT && emp 
|--
  “ (Spec bx_pre basey_pre x_digits y_digits 62 ) ”
  &&  emp
).

Definition solver_return_wit_2_split_goal_1 :=
forall (y_digits: (@list Z)) (x_digits: (@list Z)) (bx_pre: Z) (basey_pre: Z) (n_pre: Z) (m_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval > retval_2)) (PreH2 : (retval >= retval_2)) (PreH3 : (retval_2 = (numeral (basey_pre) (y_digits)))) (PreH4 : (retval = (numeral (bx_pre) (x_digits)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 10)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 10)) (PreH9 : (2 <= bx_pre)) (PreH10 : (bx_pre <= 40)) (PreH11 : (2 <= basey_pre)) (PreH12 : (basey_pre <= 40)) (PreH13 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i x_digits 0)) /\ ((Znth i x_digits 0) < bx_pre)))) (PreH14 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> ((0 <= (Znth i_2 y_digits 0)) /\ ((Znth i_2 y_digits 0) < basey_pre)))) (PreH15 : (Pre bx_pre basey_pre x_digits y_digits )) (PreH16 : (n_pre = (Zlength (x_digits)))) (PreH17 : (m_pre = (Zlength (y_digits)))),
  (Spec bx_pre basey_pre x_digits y_digits 62 )
.

Definition solver_return_wit_3 :=
(
forall (y_digits: (@list Z)) (x_digits: (@list Z)) (bx_pre: Z) (basey_pre: Z) (x_pre: Z) (n_pre: Z) (y_pre: Z) (m_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval <= retval_2)) (PreH2 : (retval >= retval_2)) (PreH3 : (retval_2 = (numeral (basey_pre) (y_digits)))) (PreH4 : (retval = (numeral (bx_pre) (x_digits)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 10)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 10)) (PreH9 : (2 <= bx_pre)) (PreH10 : (bx_pre <= 40)) (PreH11 : (2 <= basey_pre)) (PreH12 : (basey_pre <= 40)) (PreH13 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i x_digits 0)) /\ ((Znth i x_digits 0) < bx_pre)))) (PreH14 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> ((0 <= (Znth i_2 y_digits 0)) /\ ((Znth i_2 y_digits 0) < basey_pre)))) (PreH15 : (Pre bx_pre basey_pre x_digits y_digits )) (PreH16 : (n_pre = (Zlength (x_digits)))) (PreH17 : (m_pre = (Zlength (y_digits)))),
  (IntArray.full y_pre m_pre y_digits )
  **  (IntArray.full x_pre n_pre x_digits )
|--
  “ (Spec bx_pre basey_pre x_digits y_digits 61 ) ”
  &&  (IntArray.full x_pre n_pre x_digits )
  **  (IntArray.full y_pre m_pre y_digits )
) \/
(
forall (y_digits: (@list Z)) (x_digits: (@list Z)) (bx_pre: Z) (basey_pre: Z) (n_pre: Z) (m_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval <= retval_2)) (PreH2 : (retval >= retval_2)) (PreH3 : (retval_2 = (numeral (basey_pre) (y_digits)))) (PreH4 : (retval = (numeral (bx_pre) (x_digits)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 10)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 10)) (PreH9 : (2 <= bx_pre)) (PreH10 : (bx_pre <= 40)) (PreH11 : (2 <= basey_pre)) (PreH12 : (basey_pre <= 40)) (PreH13 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i x_digits 0)) /\ ((Znth i x_digits 0) < bx_pre)))) (PreH14 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> ((0 <= (Znth i_2 y_digits 0)) /\ ((Znth i_2 y_digits 0) < basey_pre)))) (PreH15 : (Pre bx_pre basey_pre x_digits y_digits )) (PreH16 : (n_pre = (Zlength (x_digits)))) (PreH17 : (m_pre = (Zlength (y_digits)))),
  TT && emp 
|--
  “ (Spec bx_pre basey_pre x_digits y_digits 61 ) ”
  &&  emp
).

Definition solver_return_wit_3_split_goal_1 :=
forall (y_digits: (@list Z)) (x_digits: (@list Z)) (bx_pre: Z) (basey_pre: Z) (n_pre: Z) (m_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval <= retval_2)) (PreH2 : (retval >= retval_2)) (PreH3 : (retval_2 = (numeral (basey_pre) (y_digits)))) (PreH4 : (retval = (numeral (bx_pre) (x_digits)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 10)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 10)) (PreH9 : (2 <= bx_pre)) (PreH10 : (bx_pre <= 40)) (PreH11 : (2 <= basey_pre)) (PreH12 : (basey_pre <= 40)) (PreH13 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i x_digits 0)) /\ ((Znth i x_digits 0) < bx_pre)))) (PreH14 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> ((0 <= (Znth i_2 y_digits 0)) /\ ((Znth i_2 y_digits 0) < basey_pre)))) (PreH15 : (Pre bx_pre basey_pre x_digits y_digits )) (PreH16 : (n_pre = (Zlength (x_digits)))) (PreH17 : (m_pre = (Zlength (y_digits)))),
  (Spec bx_pre basey_pre x_digits y_digits 61 )
.

Definition solver_partial_solve_wit_1_pure :=
(
forall (y_digits: (@list Z)) (x_digits: (@list Z)) (bx_pre: Z) (basey_pre: Z) (x_pre: Z) (n_pre: Z) (y_pre: Z) (m_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 10)) (PreH5 : (2 <= bx_pre)) (PreH6 : (bx_pre <= 40)) (PreH7 : (2 <= basey_pre)) (PreH8 : (basey_pre <= 40)) (PreH9 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i x_digits 0)) /\ ((Znth i x_digits 0) < bx_pre)))) (PreH10 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> ((0 <= (Znth i_2 y_digits 0)) /\ ((Znth i_2 y_digits 0) < basey_pre)))) (PreH11 : (Pre bx_pre basey_pre x_digits y_digits )) (PreH12 : (n_pre = (Zlength (x_digits)))) (PreH13 : (m_pre = (Zlength (y_digits)))),
  ((( &( "vx" ) )) # Int64  |->_)
  **  ((( &( "bx" ) )) # Int  |-> bx_pre)
  **  ((( &( "basey" ) )) # Int  |-> basey_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full x_pre n_pre x_digits )
  **  (IntArray.full y_pre m_pre y_digits )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 10) ”
  &&  “ (2 <= bx_pre) ”
  &&  “ (bx_pre <= 40) ”
  &&  “ (n_pre = (Zlength (x_digits))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k x_digits 0)) /\ ((Znth k x_digits 0) < bx_pre))) ”
) \/
(
forall (y_digits: (@list Z)) (x_digits: (@list Z)) (bx_pre: Z) (basey_pre: Z) (x_pre: Z) (n_pre: Z) (y_pre: Z) (m_pre: Z) (PreH1 : (m_pre <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (basey_pre <= INT_MAX)) (PreH4 : (bx_pre <= INT_MAX)) (PreH5 : (m_pre >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (basey_pre >= INT_MIN)) (PreH8 : (bx_pre >= INT_MIN)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 10)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10)) (PreH13 : (2 <= bx_pre)) (PreH14 : (bx_pre <= 40)) (PreH15 : (2 <= basey_pre)) (PreH16 : (basey_pre <= 40)) (PreH17 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i x_digits 0)) /\ ((Znth i x_digits 0) < bx_pre)))) (PreH18 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> ((0 <= (Znth i_2 y_digits 0)) /\ ((Znth i_2 y_digits 0) < basey_pre)))) (PreH19 : (Pre bx_pre basey_pre x_digits y_digits )) (PreH20 : (n_pre = (Zlength (x_digits)))) (PreH21 : (m_pre = (Zlength (y_digits)))),
  ((( &( "vx" ) )) # Int64  |->_)
  **  ((( &( "bx" ) )) # Int  |-> bx_pre)
  **  ((( &( "basey" ) )) # Int  |-> basey_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full x_pre n_pre x_digits )
  **  (IntArray.full y_pre m_pre y_digits )
|--
  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k x_digits 0)) /\ ((Znth k x_digits 0) < bx_pre))) ”
).

Definition solver_partial_solve_wit_1_pure_split_goal_1 :=
forall (y_digits: (@list Z)) (x_digits: (@list Z)) (bx_pre: Z) (basey_pre: Z) (x_pre: Z) (n_pre: Z) (y_pre: Z) (m_pre: Z) (PreH1 : (m_pre <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (basey_pre <= INT_MAX)) (PreH4 : (bx_pre <= INT_MAX)) (PreH5 : (m_pre >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (basey_pre >= INT_MIN)) (PreH8 : (bx_pre >= INT_MIN)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 10)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10)) (PreH13 : (2 <= bx_pre)) (PreH14 : (bx_pre <= 40)) (PreH15 : (2 <= basey_pre)) (PreH16 : (basey_pre <= 40)) (PreH17 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i x_digits 0)) /\ ((Znth i x_digits 0) < bx_pre)))) (PreH18 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> ((0 <= (Znth i_2 y_digits 0)) /\ ((Znth i_2 y_digits 0) < basey_pre)))) (PreH19 : (Pre bx_pre basey_pre x_digits y_digits )) (PreH20 : (n_pre = (Zlength (x_digits)))) (PreH21 : (m_pre = (Zlength (y_digits)))),
  ((( &( "vx" ) )) # Int64  |->_)
  **  ((( &( "bx" ) )) # Int  |-> bx_pre)
  **  ((( &( "basey" ) )) # Int  |-> basey_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full x_pre n_pre x_digits )
  **  (IntArray.full y_pre m_pre y_digits )
|--
  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k x_digits 0)) /\ ((Znth k x_digits 0) < bx_pre))) ”
.

Definition solver_partial_solve_wit_1_aux :=
forall (y_digits: (@list Z)) (x_digits: (@list Z)) (bx_pre: Z) (basey_pre: Z) (x_pre: Z) (n_pre: Z) (y_pre: Z) (m_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 10)) (PreH5 : (2 <= bx_pre)) (PreH6 : (bx_pre <= 40)) (PreH7 : (2 <= basey_pre)) (PreH8 : (basey_pre <= 40)) (PreH9 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i x_digits 0)) /\ ((Znth i x_digits 0) < bx_pre)))) (PreH10 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> ((0 <= (Znth i_2 y_digits 0)) /\ ((Znth i_2 y_digits 0) < basey_pre)))) (PreH11 : (Pre bx_pre basey_pre x_digits y_digits )) (PreH12 : (n_pre = (Zlength (x_digits)))) (PreH13 : (m_pre = (Zlength (y_digits)))),
  (IntArray.full x_pre n_pre x_digits )
  **  (IntArray.full y_pre m_pre y_digits )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 10) ”
  &&  “ (2 <= bx_pre) ”
  &&  “ (bx_pre <= 40) ”
  &&  “ (n_pre = (Zlength (x_digits))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k x_digits 0)) /\ ((Znth k x_digits 0) < bx_pre))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 10) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 10) ”
  &&  “ (2 <= bx_pre) ”
  &&  “ (bx_pre <= 40) ”
  &&  “ (2 <= basey_pre) ”
  &&  “ (basey_pre <= 40) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i x_digits 0)) /\ ((Znth i x_digits 0) < bx_pre))) ”
  &&  “ forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> ((0 <= (Znth i_2 y_digits 0)) /\ ((Znth i_2 y_digits 0) < basey_pre))) ”
  &&  “ (Pre bx_pre basey_pre x_digits y_digits ) ”
  &&  “ (n_pre = (Zlength (x_digits))) ”
  &&  “ (m_pre = (Zlength (y_digits))) ”
  &&  (IntArray.full x_pre n_pre x_digits )
  **  (IntArray.full y_pre m_pre y_digits )
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2_pure :=
(
forall (y_digits: (@list Z)) (x_digits: (@list Z)) (bx_pre: Z) (basey_pre: Z) (x_pre: Z) (n_pre: Z) (y_pre: Z) (m_pre: Z) (retval: Z) (PreH1 : (retval = (numeral (bx_pre) (x_digits)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 10)) (PreH6 : (2 <= bx_pre)) (PreH7 : (bx_pre <= 40)) (PreH8 : (2 <= basey_pre)) (PreH9 : (basey_pre <= 40)) (PreH10 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i x_digits 0)) /\ ((Znth i x_digits 0) < bx_pre)))) (PreH11 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> ((0 <= (Znth i_2 y_digits 0)) /\ ((Znth i_2 y_digits 0) < basey_pre)))) (PreH12 : (Pre bx_pre basey_pre x_digits y_digits )) (PreH13 : (n_pre = (Zlength (x_digits)))) (PreH14 : (m_pre = (Zlength (y_digits)))),
  ((( &( "vy" ) )) # Int64  |->_)
  **  (IntArray.full x_pre n_pre x_digits )
  **  ((( &( "vx" ) )) # Int64  |-> retval)
  **  ((( &( "bx" ) )) # Int  |-> bx_pre)
  **  ((( &( "basey" ) )) # Int  |-> basey_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full y_pre m_pre y_digits )
|--
  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 10) ”
  &&  “ (2 <= basey_pre) ”
  &&  “ (basey_pre <= 40) ”
  &&  “ (m_pre = (Zlength (y_digits))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < m_pre)) -> ((0 <= (Znth k y_digits 0)) /\ ((Znth k y_digits 0) < basey_pre))) ”
) \/
(
forall (y_digits: (@list Z)) (x_digits: (@list Z)) (bx_pre: Z) (basey_pre: Z) (x_pre: Z) (n_pre: Z) (y_pre: Z) (m_pre: Z) (retval: Z) (PreH1 : (retval <= INT64_MAX)) (PreH2 : (retval >= INT64_MIN)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (basey_pre <= INT_MAX)) (PreH6 : (bx_pre <= INT_MAX)) (PreH7 : (m_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (basey_pre >= INT_MIN)) (PreH10 : (bx_pre >= INT_MIN)) (PreH11 : (retval = (numeral (bx_pre) (x_digits)))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 10)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 10)) (PreH16 : (2 <= bx_pre)) (PreH17 : (bx_pre <= 40)) (PreH18 : (2 <= basey_pre)) (PreH19 : (basey_pre <= 40)) (PreH20 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i x_digits 0)) /\ ((Znth i x_digits 0) < bx_pre)))) (PreH21 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> ((0 <= (Znth i_2 y_digits 0)) /\ ((Znth i_2 y_digits 0) < basey_pre)))) (PreH22 : (Pre bx_pre basey_pre x_digits y_digits )) (PreH23 : (n_pre = (Zlength (x_digits)))) (PreH24 : (m_pre = (Zlength (y_digits)))),
  ((( &( "vy" ) )) # Int64  |->_)
  **  (IntArray.full x_pre n_pre x_digits )
  **  ((( &( "vx" ) )) # Int64  |-> retval)
  **  ((( &( "bx" ) )) # Int  |-> bx_pre)
  **  ((( &( "basey" ) )) # Int  |-> basey_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full y_pre m_pre y_digits )
|--
  “ forall (k: Z), (((0 <= k) /\ (k < m_pre)) -> ((0 <= (Znth k y_digits 0)) /\ ((Znth k y_digits 0) < basey_pre))) ”
).

Definition solver_partial_solve_wit_2_pure_split_goal_1 :=
forall (y_digits: (@list Z)) (x_digits: (@list Z)) (bx_pre: Z) (basey_pre: Z) (x_pre: Z) (n_pre: Z) (y_pre: Z) (m_pre: Z) (retval: Z) (PreH1 : (retval <= INT64_MAX)) (PreH2 : (retval >= INT64_MIN)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (basey_pre <= INT_MAX)) (PreH6 : (bx_pre <= INT_MAX)) (PreH7 : (m_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (basey_pre >= INT_MIN)) (PreH10 : (bx_pre >= INT_MIN)) (PreH11 : (retval = (numeral (bx_pre) (x_digits)))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 10)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 10)) (PreH16 : (2 <= bx_pre)) (PreH17 : (bx_pre <= 40)) (PreH18 : (2 <= basey_pre)) (PreH19 : (basey_pre <= 40)) (PreH20 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i x_digits 0)) /\ ((Znth i x_digits 0) < bx_pre)))) (PreH21 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> ((0 <= (Znth i_2 y_digits 0)) /\ ((Znth i_2 y_digits 0) < basey_pre)))) (PreH22 : (Pre bx_pre basey_pre x_digits y_digits )) (PreH23 : (n_pre = (Zlength (x_digits)))) (PreH24 : (m_pre = (Zlength (y_digits)))),
  ((( &( "vy" ) )) # Int64  |->_)
  **  (IntArray.full x_pre n_pre x_digits )
  **  ((( &( "vx" ) )) # Int64  |-> retval)
  **  ((( &( "bx" ) )) # Int  |-> bx_pre)
  **  ((( &( "basey" ) )) # Int  |-> basey_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full y_pre m_pre y_digits )
|--
  “ forall (k: Z), (((0 <= k) /\ (k < m_pre)) -> ((0 <= (Znth k y_digits 0)) /\ ((Znth k y_digits 0) < basey_pre))) ”
.

Definition solver_partial_solve_wit_2_aux :=
forall (y_digits: (@list Z)) (x_digits: (@list Z)) (bx_pre: Z) (basey_pre: Z) (x_pre: Z) (n_pre: Z) (y_pre: Z) (m_pre: Z) (retval: Z) (PreH1 : (retval = (numeral (bx_pre) (x_digits)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 10)) (PreH6 : (2 <= bx_pre)) (PreH7 : (bx_pre <= 40)) (PreH8 : (2 <= basey_pre)) (PreH9 : (basey_pre <= 40)) (PreH10 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i x_digits 0)) /\ ((Znth i x_digits 0) < bx_pre)))) (PreH11 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> ((0 <= (Znth i_2 y_digits 0)) /\ ((Znth i_2 y_digits 0) < basey_pre)))) (PreH12 : (Pre bx_pre basey_pre x_digits y_digits )) (PreH13 : (n_pre = (Zlength (x_digits)))) (PreH14 : (m_pre = (Zlength (y_digits)))),
  (IntArray.full x_pre n_pre x_digits )
  **  (IntArray.full y_pre m_pre y_digits )
|--
  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 10) ”
  &&  “ (2 <= basey_pre) ”
  &&  “ (basey_pre <= 40) ”
  &&  “ (m_pre = (Zlength (y_digits))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < m_pre)) -> ((0 <= (Znth k y_digits 0)) /\ ((Znth k y_digits 0) < basey_pre))) ”
  &&  “ (retval = (numeral (bx_pre) (x_digits))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 10) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 10) ”
  &&  “ (2 <= bx_pre) ”
  &&  “ (bx_pre <= 40) ”
  &&  “ (2 <= basey_pre) ”
  &&  “ (basey_pre <= 40) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i x_digits 0)) /\ ((Znth i x_digits 0) < bx_pre))) ”
  &&  “ forall (i_2: Z), (((0 <= i_2) /\ (i_2 < m_pre)) -> ((0 <= (Znth i_2 y_digits 0)) /\ ((Znth i_2 y_digits 0) < basey_pre))) ”
  &&  “ (Pre bx_pre basey_pre x_digits y_digits ) ”
  &&  “ (n_pre = (Zlength (x_digits))) ”
  &&  “ (m_pre = (Zlength (y_digits))) ”
  &&  (IntArray.full y_pre m_pre y_digits )
  **  (IntArray.full x_pre n_pre x_digits )
.

Definition solver_partial_solve_wit_2 := solver_partial_solve_wit_2_pure -> solver_partial_solve_wit_2_aux.

Module Type VC_Correct.


Axiom proof_of_numeral_value_safety_wit_1 : numeral_value_safety_wit_1.
Axiom proof_of_numeral_value_safety_wit_2 : numeral_value_safety_wit_2.
Axiom proof_of_numeral_value_safety_wit_3 : numeral_value_safety_wit_3.
Axiom proof_of_numeral_value_safety_wit_4 : numeral_value_safety_wit_4.
Axiom proof_of_numeral_value_safety_wit_5 : numeral_value_safety_wit_5.
Axiom proof_of_numeral_value_entail_wit_1 : numeral_value_entail_wit_1.
Axiom proof_of_numeral_value_entail_wit_2 : numeral_value_entail_wit_2.
Axiom proof_of_numeral_value_return_wit_1 : numeral_value_return_wit_1.
Axiom proof_of_numeral_value_partial_solve_wit_1 : numeral_value_partial_solve_wit_1.
Axiom proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Axiom proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Axiom proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_return_wit_3 : solver_return_wit_3.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.

End VC_Correct.
