From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_base_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_proof.

(*----- Function gmp_abs -----*)

Definition gmp_abs_safety_wit_1 :=
forall (x_pre: Z) (PreH1 : (INT_MIN < x_pre)) (PreH2 : (x_pre <= INT_MAX)),
  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition gmp_abs_safety_wit_2 :=
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)),
  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (x_pre <> (INT_MIN)) ”
.

Definition gmp_abs_return_wit_1 :=
(
forall (x_pre: Z) (PreH1 : (x_pre >= 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)),
  TT && emp 
|--
  “ (x_pre = (Zabs (x_pre))) ”
  &&  emp
) \/
(
forall (x_pre: Z) (PreH1 : (x_pre >= 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)),
  TT && emp 
|--
  “ (x_pre = (Zabs (x_pre))) ”
  &&  emp
).

Definition gmp_abs_return_wit_1_split_goal_1 :=
forall (x_pre: Z) (PreH1 : (x_pre >= 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)),
  (x_pre = (Zabs (x_pre)))
.

Definition gmp_abs_return_wit_2 :=
(
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)),
  TT && emp 
|--
  “ ((-x_pre) = (Zabs (x_pre))) ”
  &&  emp
) \/
(
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)),
  TT && emp 
|--
  “ ((-x_pre) = (Zabs (x_pre))) ”
  &&  emp
).

Definition gmp_abs_return_wit_2_split_goal_1 :=
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)),
  ((-x_pre) = (Zabs (x_pre)))
.

(*----- Function gmp_max -----*)

Definition gmp_max_return_wit_1 :=
(
forall (a_pre: Z) (b_pre: Z) (PreH1 : (a_pre > b_pre)),
  TT && emp 
|--
  “ (a_pre = (Z.max (a_pre) (b_pre))) ”
  &&  emp
) \/
(
forall (a_pre: Z) (b_pre: Z) (PreH1 : (a_pre > b_pre)),
  TT && emp 
|--
  “ (a_pre = (Z.max (a_pre) (b_pre))) ”
  &&  emp
).

Definition gmp_max_return_wit_1_split_goal_1 :=
forall (a_pre: Z) (b_pre: Z) (PreH1 : (a_pre > b_pre)),
  (a_pre = (Z.max (a_pre) (b_pre)))
.

Definition gmp_max_return_wit_2 :=
(
forall (a_pre: Z) (b_pre: Z) (PreH1 : (a_pre <= b_pre)),
  TT && emp 
|--
  “ (b_pre = (Z.max (a_pre) (b_pre))) ”
  &&  emp
) \/
(
forall (a_pre: Z) (b_pre: Z) (PreH1 : (a_pre <= b_pre)),
  TT && emp 
|--
  “ (b_pre = (Z.max (a_pre) (b_pre))) ”
  &&  emp
).

Definition gmp_max_return_wit_2_split_goal_1 :=
forall (a_pre: Z) (b_pre: Z) (PreH1 : (a_pre <= b_pre)),
  (b_pre = (Z.max (a_pre) (b_pre)))
.

(*----- Function gmp_cmp -----*)

Definition gmp_cmp_safety_wit_1 :=
forall (a_pre: Z) (b_pre: Z) (PreH1 : (a_pre >= b_pre)) (PreH2 : (a_pre > b_pre)),
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  “ ((1 - 0 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (1 - 0 )) ”
.

Definition gmp_cmp_safety_wit_2 :=
forall (a_pre: Z) (b_pre: Z) (PreH1 : (a_pre < b_pre)) (PreH2 : (a_pre <= b_pre)),
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  “ ((0 - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (0 - 1 )) ”
.

Definition gmp_cmp_safety_wit_3 :=
forall (a_pre: Z) (b_pre: Z) (PreH1 : (a_pre >= b_pre)) (PreH2 : (a_pre <= b_pre)),
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  “ ((0 - 0 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (0 - 0 )) ”
.

Definition gmp_cmp_safety_wit_4 :=
forall (a_pre: Z) (b_pre: Z) (PreH1 : (a_pre < b_pre)) (PreH2 : (a_pre > b_pre)),
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
|--
  “ False ”
.

Definition gmp_cmp_return_wit_1 :=
forall (a_pre: Z) (b_pre: Z) (PreH1 : (a_pre >= b_pre)) (PreH2 : (a_pre <= b_pre)),
  TT && emp 
|--
  “ (a_pre = b_pre) ”
  &&  “ ((0 - 0 ) = 0) ”
  &&  emp
.

Definition gmp_cmp_return_wit_2 :=
forall (a_pre: Z) (b_pre: Z) (PreH1 : (a_pre < b_pre)) (PreH2 : (a_pre <= b_pre)),
  TT && emp 
|--
  “ (a_pre < b_pre) ”
  &&  “ ((0 - 1 ) = (-1)) ”
  &&  emp
.

Definition gmp_cmp_return_wit_3 :=
forall (a_pre: Z) (b_pre: Z) (PreH1 : (a_pre >= b_pre)) (PreH2 : (a_pre > b_pre)),
  TT && emp 
|--
  “ (a_pre > b_pre) ”
  &&  “ ((1 - 0 ) = 1) ”
  &&  emp
.

(*----- Function mpn_cmp -----*)

Definition mpn_cmp_safety_wit_1 :=
forall (val2: Z) (val1: Z) (ap_pre: Z) (bp_pre: Z) (n_pre: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH2 : ((last (l1) (1)) >= 1)) (PreH3 : (list_within_bound UINT_MOD l1 )) (PreH4 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH5 : ((last (l2) (1)) >= 1)) (PreH6 : (list_within_bound UINT_MOD l2 )) (PreH7 : (n_pre = (Zlength (l1)))) (PreH8 : (n_pre = (Zlength (l2)))) (PreH9 : (0 <= n_pre)),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.full ap_pre n_pre l1 )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.full bp_pre n_pre l2 )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition mpn_cmp_safety_wit_2 :=
forall (val2: Z) (val1: Z) (ap_pre: Z) (bp_pre: Z) (n_pre: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((-1) <= n)) (PreH2 : (n < n_pre)) (PreH3 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH4 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH5 : ((last (l1) (1)) >= 1)) (PreH6 : (list_within_bound UINT_MOD l1 )) (PreH7 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH8 : ((last (l2) (1)) >= 1)) (PreH9 : (list_within_bound UINT_MOD l2 )),
  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.full ap_pre n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_cmp_safety_wit_3 :=
forall (val2: Z) (val1: Z) (ap_pre: Z) (bp_pre: Z) (n_pre: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((Znth n l1 0) > (Znth n l2 0))) (PreH2 : ((Znth n l1 0) <> (Znth n l2 0))) (PreH3 : (n >= 0)) (PreH4 : ((-1) <= n)) (PreH5 : (n < n_pre)) (PreH6 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH7 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH8 : ((last (l1) (1)) >= 1)) (PreH9 : (list_within_bound UINT_MOD l1 )) (PreH10 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH11 : ((last (l2) (1)) >= 1)) (PreH12 : (list_within_bound UINT_MOD l2 )),
  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_cmp_safety_wit_4 :=
forall (val2: Z) (val1: Z) (ap_pre: Z) (bp_pre: Z) (n_pre: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((Znth n l1 0) <= (Znth n l2 0))) (PreH2 : ((Znth n l1 0) <> (Znth n l2 0))) (PreH3 : (n >= 0)) (PreH4 : ((-1) <= n)) (PreH5 : (n < n_pre)) (PreH6 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH7 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH8 : ((last (l1) (1)) >= 1)) (PreH9 : (list_within_bound UINT_MOD l1 )) (PreH10 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH11 : ((last (l2) (1)) >= 1)) (PreH12 : (list_within_bound UINT_MOD l2 )),
  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition mpn_cmp_safety_wit_5 :=
forall (val2: Z) (val1: Z) (ap_pre: Z) (bp_pre: Z) (n_pre: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((Znth n l1 0) <= (Znth n l2 0))) (PreH2 : ((Znth n l1 0) <> (Znth n l2 0))) (PreH3 : (n >= 0)) (PreH4 : ((-1) <= n)) (PreH5 : (n < n_pre)) (PreH6 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH7 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH8 : ((last (l1) (1)) >= 1)) (PreH9 : (list_within_bound UINT_MOD l1 )) (PreH10 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH11 : ((last (l2) (1)) >= 1)) (PreH12 : (list_within_bound UINT_MOD l2 )),
  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_cmp_safety_wit_6 :=
forall (val2: Z) (val1: Z) (ap_pre: Z) (bp_pre: Z) (n_pre: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((Znth n l1 0) = (Znth n l2 0))) (PreH2 : (n >= 0)) (PreH3 : ((-1) <= n)) (PreH4 : (n < n_pre)) (PreH5 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH6 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH7 : ((last (l1) (1)) >= 1)) (PreH8 : (list_within_bound UINT_MOD l1 )) (PreH9 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH10 : ((last (l2) (1)) >= 1)) (PreH11 : (list_within_bound UINT_MOD l2 )),
  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ ((n - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n - 1 )) ”
.

Definition mpn_cmp_safety_wit_7 :=
forall (val2: Z) (val1: Z) (ap_pre: Z) (bp_pre: Z) (n_pre: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : (n < 0)) (PreH2 : ((-1) <= n)) (PreH3 : (n < n_pre)) (PreH4 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH5 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH6 : ((last (l1) (1)) >= 1)) (PreH7 : (list_within_bound UINT_MOD l1 )) (PreH8 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH9 : ((last (l2) (1)) >= 1)) (PreH10 : (list_within_bound UINT_MOD l2 )),
  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.full ap_pre n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_cmp_entail_wit_1 :=
(
forall (val2: Z) (val1: Z) (ap_pre: Z) (bp_pre: Z) (n_pre: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH2 : ((last (l1) (1)) >= 1)) (PreH3 : (list_within_bound UINT_MOD l1 )) (PreH4 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH5 : ((last (l2) (1)) >= 1)) (PreH6 : (list_within_bound UINT_MOD l2 )) (PreH7 : (n_pre = (Zlength (l1)))) (PreH8 : (n_pre = (Zlength (l2)))) (PreH9 : (0 <= n_pre)),
  (UIntArray.full ap_pre n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
|--
  “ ((-1) <= (n_pre - 1 )) ”
  &&  “ ((n_pre - 1 ) < n_pre) ”
  &&  “ ((sublist (((n_pre - 1 ) + 1 )) (n_pre) (l1)) = (sublist (((n_pre - 1 ) + 1 )) (n_pre) (l2))) ”
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = val1) ”
  &&  “ ((last (l1) (1)) >= 1) ”
  &&  “ (list_within_bound UINT_MOD l1 ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = val2) ”
  &&  “ ((last (l2) (1)) >= 1) ”
  &&  “ (list_within_bound UINT_MOD l2 ) ”
  &&  (UIntArray.full ap_pre n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
) \/
(
forall (val2: Z) (val1: Z) (n_pre: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH2 : ((last (l1) (1)) >= 1)) (PreH3 : (list_within_bound UINT_MOD l1 )) (PreH4 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH5 : ((last (l2) (1)) >= 1)) (PreH6 : (list_within_bound UINT_MOD l2 )) (PreH7 : (n_pre = (Zlength (l1)))) (PreH8 : (n_pre = (Zlength (l2)))) (PreH9 : (0 <= n_pre)),
  TT && emp 
|--
  “ ((sublist (((n_pre - 1 ) + 1 )) (n_pre) (l1)) = (sublist (((n_pre - 1 ) + 1 )) (n_pre) (l2))) ”
  &&  emp
).

Definition mpn_cmp_entail_wit_1_split_goal_1 :=
forall (val2: Z) (val1: Z) (n_pre: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH2 : ((last (l1) (1)) >= 1)) (PreH3 : (list_within_bound UINT_MOD l1 )) (PreH4 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH5 : ((last (l2) (1)) >= 1)) (PreH6 : (list_within_bound UINT_MOD l2 )) (PreH7 : (n_pre = (Zlength (l1)))) (PreH8 : (n_pre = (Zlength (l2)))) (PreH9 : (0 <= n_pre)),
  ((sublist (((n_pre - 1 ) + 1 )) (n_pre) (l1)) = (sublist (((n_pre - 1 ) + 1 )) (n_pre) (l2)))
.

Definition mpn_cmp_entail_wit_2 :=
(
forall (val2: Z) (val1: Z) (ap_pre: Z) (bp_pre: Z) (n_pre: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((Znth n l1 0) = (Znth n l2 0))) (PreH2 : (n >= 0)) (PreH3 : ((-1) <= n)) (PreH4 : (n < n_pre)) (PreH5 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH6 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH7 : ((last (l1) (1)) >= 1)) (PreH8 : (list_within_bound UINT_MOD l1 )) (PreH9 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH10 : ((last (l2) (1)) >= 1)) (PreH11 : (list_within_bound UINT_MOD l2 )),
  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
|--
  “ ((-1) <= (n - 1 )) ”
  &&  “ ((n - 1 ) < n_pre) ”
  &&  “ ((sublist (((n - 1 ) + 1 )) (n_pre) (l1)) = (sublist (((n - 1 ) + 1 )) (n_pre) (l2))) ”
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = val1) ”
  &&  “ ((last (l1) (1)) >= 1) ”
  &&  “ (list_within_bound UINT_MOD l1 ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = val2) ”
  &&  “ ((last (l2) (1)) >= 1) ”
  &&  “ (list_within_bound UINT_MOD l2 ) ”
  &&  (UIntArray.full ap_pre n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
) \/
(
forall (val2: Z) (val1: Z) (n_pre: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((Znth n l1 0) = (Znth n l2 0))) (PreH2 : (n >= 0)) (PreH3 : ((-1) <= n)) (PreH4 : (n < n_pre)) (PreH5 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH6 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH7 : ((last (l1) (1)) >= 1)) (PreH8 : (list_within_bound UINT_MOD l1 )) (PreH9 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH10 : ((last (l2) (1)) >= 1)) (PreH11 : (list_within_bound UINT_MOD l2 )),
  TT && emp 
|--
  “ ((sublist (((n - 1 ) + 1 )) (n_pre) (l1)) = (sublist (((n - 1 ) + 1 )) (n_pre) (l2))) ”
  &&  emp
).

Definition mpn_cmp_entail_wit_2_split_goal_1 :=
forall (val2: Z) (val1: Z) (n_pre: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((Znth n l1 0) = (Znth n l2 0))) (PreH2 : (n >= 0)) (PreH3 : ((-1) <= n)) (PreH4 : (n < n_pre)) (PreH5 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH6 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH7 : ((last (l1) (1)) >= 1)) (PreH8 : (list_within_bound UINT_MOD l1 )) (PreH9 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH10 : ((last (l2) (1)) >= 1)) (PreH11 : (list_within_bound UINT_MOD l2 )),
  ((sublist (((n - 1 ) + 1 )) (n_pre) (l1)) = (sublist (((n - 1 ) + 1 )) (n_pre) (l2)))
.

Definition mpn_cmp_return_wit_1 :=
(
forall (val2: Z) (val1: Z) (ap_pre: Z) (bp_pre: Z) (n_pre: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : (n < 0)) (PreH2 : ((-1) <= n)) (PreH3 : (n < n_pre)) (PreH4 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH5 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH6 : ((last (l1) (1)) >= 1)) (PreH7 : (list_within_bound UINT_MOD l1 )) (PreH8 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH9 : ((last (l2) (1)) >= 1)) (PreH10 : (list_within_bound UINT_MOD l2 )),
  (UIntArray.full ap_pre n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
|--
  “ (val1 = val2) ”
  &&  “ (0 = 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre )
) \/
(
forall (val2: Z) (val1: Z) (ap_pre: Z) (bp_pre: Z) (n_pre: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : (n < 0)) (PreH2 : ((-1) <= n)) (PreH3 : (n < n_pre)) (PreH4 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH5 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH6 : ((last (l1) (1)) >= 1)) (PreH7 : (list_within_bound UINT_MOD l1 )) (PreH8 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH9 : ((last (l2) (1)) >= 1)) (PreH10 : (list_within_bound UINT_MOD l2 )),
  (UIntArray.full ap_pre n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
|--
  “ (val1 = val2) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre )
).

Definition mpn_cmp_return_wit_1_split_goal_1 :=
forall (val2: Z) (val1: Z) (ap_pre: Z) (bp_pre: Z) (n_pre: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : (n < 0)) (PreH2 : ((-1) <= n)) (PreH3 : (n < n_pre)) (PreH4 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH5 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH6 : ((last (l1) (1)) >= 1)) (PreH7 : (list_within_bound UINT_MOD l1 )) (PreH8 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH9 : ((last (l2) (1)) >= 1)) (PreH10 : (list_within_bound UINT_MOD l2 )),
  (UIntArray.full ap_pre n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
|--
  “ (val1 = val2) ”
.

Definition mpn_cmp_return_wit_1_split_goal_spatial :=
forall (val2: Z) (val1: Z) (ap_pre: Z) (bp_pre: Z) (n_pre: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : (n < 0)) (PreH2 : ((-1) <= n)) (PreH3 : (n < n_pre)) (PreH4 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH5 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH6 : ((last (l1) (1)) >= 1)) (PreH7 : (list_within_bound UINT_MOD l1 )) (PreH8 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH9 : ((last (l2) (1)) >= 1)) (PreH10 : (list_within_bound UINT_MOD l2 )),
  (UIntArray.full ap_pre n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
|--
  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre )
.

Definition mpn_cmp_return_wit_2 :=
(
forall (val2: Z) (val1: Z) (ap_pre: Z) (bp_pre: Z) (n_pre: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((Znth n l1 0) > (Znth n l2 0))) (PreH2 : ((Znth n l1 0) <> (Znth n l2 0))) (PreH3 : (n >= 0)) (PreH4 : ((-1) <= n)) (PreH5 : (n < n_pre)) (PreH6 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH7 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH8 : ((last (l1) (1)) >= 1)) (PreH9 : (list_within_bound UINT_MOD l1 )) (PreH10 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH11 : ((last (l2) (1)) >= 1)) (PreH12 : (list_within_bound UINT_MOD l2 )),
  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
|--
  “ (val1 > val2) ”
  &&  “ (1 = 1) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre )
) \/
(
forall (val2: Z) (val1: Z) (ap_pre: Z) (bp_pre: Z) (n_pre: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((Znth n l1 0) > (Znth n l2 0))) (PreH2 : ((Znth n l1 0) <> (Znth n l2 0))) (PreH3 : (n >= 0)) (PreH4 : ((-1) <= n)) (PreH5 : (n < n_pre)) (PreH6 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH7 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH8 : ((last (l1) (1)) >= 1)) (PreH9 : (list_within_bound UINT_MOD l1 )) (PreH10 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH11 : ((last (l2) (1)) >= 1)) (PreH12 : (list_within_bound UINT_MOD l2 )),
  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
|--
  “ (val1 > val2) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre )
).

Definition mpn_cmp_return_wit_2_split_goal_1 :=
forall (val2: Z) (val1: Z) (ap_pre: Z) (bp_pre: Z) (n_pre: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((Znth n l1 0) > (Znth n l2 0))) (PreH2 : ((Znth n l1 0) <> (Znth n l2 0))) (PreH3 : (n >= 0)) (PreH4 : ((-1) <= n)) (PreH5 : (n < n_pre)) (PreH6 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH7 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH8 : ((last (l1) (1)) >= 1)) (PreH9 : (list_within_bound UINT_MOD l1 )) (PreH10 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH11 : ((last (l2) (1)) >= 1)) (PreH12 : (list_within_bound UINT_MOD l2 )),
  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
|--
  “ (val1 > val2) ”
.

Definition mpn_cmp_return_wit_2_split_goal_spatial :=
forall (val2: Z) (val1: Z) (ap_pre: Z) (bp_pre: Z) (n_pre: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((Znth n l1 0) > (Znth n l2 0))) (PreH2 : ((Znth n l1 0) <> (Znth n l2 0))) (PreH3 : (n >= 0)) (PreH4 : ((-1) <= n)) (PreH5 : (n < n_pre)) (PreH6 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH7 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH8 : ((last (l1) (1)) >= 1)) (PreH9 : (list_within_bound UINT_MOD l1 )) (PreH10 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH11 : ((last (l2) (1)) >= 1)) (PreH12 : (list_within_bound UINT_MOD l2 )),
  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
|--
  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre )
.

Definition mpn_cmp_return_wit_3 :=
(
forall (val2: Z) (val1: Z) (ap_pre: Z) (bp_pre: Z) (n_pre: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((Znth n l1 0) <= (Znth n l2 0))) (PreH2 : ((Znth n l1 0) <> (Znth n l2 0))) (PreH3 : (n >= 0)) (PreH4 : ((-1) <= n)) (PreH5 : (n < n_pre)) (PreH6 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH7 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH8 : ((last (l1) (1)) >= 1)) (PreH9 : (list_within_bound UINT_MOD l1 )) (PreH10 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH11 : ((last (l2) (1)) >= 1)) (PreH12 : (list_within_bound UINT_MOD l2 )),
  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
|--
  “ (val1 < val2) ”
  &&  “ ((-1) = (-1)) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre )
) \/
(
forall (val2: Z) (val1: Z) (ap_pre: Z) (bp_pre: Z) (n_pre: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((Znth n l1 0) <= (Znth n l2 0))) (PreH2 : ((Znth n l1 0) <> (Znth n l2 0))) (PreH3 : (n >= 0)) (PreH4 : ((-1) <= n)) (PreH5 : (n < n_pre)) (PreH6 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH7 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH8 : ((last (l1) (1)) >= 1)) (PreH9 : (list_within_bound UINT_MOD l1 )) (PreH10 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH11 : ((last (l2) (1)) >= 1)) (PreH12 : (list_within_bound UINT_MOD l2 )),
  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
|--
  “ (val1 < val2) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre )
).

Definition mpn_cmp_return_wit_3_split_goal_1 :=
forall (val2: Z) (val1: Z) (ap_pre: Z) (bp_pre: Z) (n_pre: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((Znth n l1 0) <= (Znth n l2 0))) (PreH2 : ((Znth n l1 0) <> (Znth n l2 0))) (PreH3 : (n >= 0)) (PreH4 : ((-1) <= n)) (PreH5 : (n < n_pre)) (PreH6 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH7 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH8 : ((last (l1) (1)) >= 1)) (PreH9 : (list_within_bound UINT_MOD l1 )) (PreH10 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH11 : ((last (l2) (1)) >= 1)) (PreH12 : (list_within_bound UINT_MOD l2 )),
  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
|--
  “ (val1 < val2) ”
.

Definition mpn_cmp_return_wit_3_split_goal_spatial :=
forall (val2: Z) (val1: Z) (ap_pre: Z) (bp_pre: Z) (n_pre: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((Znth n l1 0) <= (Znth n l2 0))) (PreH2 : ((Znth n l1 0) <> (Znth n l2 0))) (PreH3 : (n >= 0)) (PreH4 : ((-1) <= n)) (PreH5 : (n < n_pre)) (PreH6 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH7 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH8 : ((last (l1) (1)) >= 1)) (PreH9 : (list_within_bound UINT_MOD l1 )) (PreH10 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH11 : ((last (l2) (1)) >= 1)) (PreH12 : (list_within_bound UINT_MOD l2 )),
  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
|--
  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre )
.

Definition mpn_cmp_partial_solve_wit_1 :=
forall (val2: Z) (val1: Z) (ap_pre: Z) (bp_pre: Z) (n_pre: Z) (PreH1 : (0 <= n_pre)),
  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre )
|--
  “ (0 <= n_pre) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre )
.

Definition mpn_cmp_partial_solve_wit_2 :=
forall (val2: Z) (val1: Z) (ap_pre: Z) (bp_pre: Z) (n_pre: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : (n >= 0)) (PreH2 : ((-1) <= n)) (PreH3 : (n < n_pre)) (PreH4 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH5 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH6 : ((last (l1) (1)) >= 1)) (PreH7 : (list_within_bound UINT_MOD l1 )) (PreH8 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH9 : ((last (l2) (1)) >= 1)) (PreH10 : (list_within_bound UINT_MOD l2 )),
  (UIntArray.full ap_pre n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
|--
  “ (n >= 0) ”
  &&  “ ((-1) <= n) ”
  &&  “ (n < n_pre) ”
  &&  “ ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) ”
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = val1) ”
  &&  “ ((last (l1) (1)) >= 1) ”
  &&  “ (list_within_bound UINT_MOD l1 ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = val2) ”
  &&  “ ((last (l2) (1)) >= 1) ”
  &&  “ (list_within_bound UINT_MOD l2 ) ”
  &&  (((ap_pre + (n * sizeof(UINT)))) # UInt  |-> (Znth n l1 0))
  **  (UIntArray.missing_i ap_pre n 0 n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
.

Definition mpn_cmp_partial_solve_wit_3 :=
forall (val2: Z) (val1: Z) (ap_pre: Z) (bp_pre: Z) (n_pre: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : (n >= 0)) (PreH2 : ((-1) <= n)) (PreH3 : (n < n_pre)) (PreH4 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH5 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH6 : ((last (l1) (1)) >= 1)) (PreH7 : (list_within_bound UINT_MOD l1 )) (PreH8 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH9 : ((last (l2) (1)) >= 1)) (PreH10 : (list_within_bound UINT_MOD l2 )),
  (UIntArray.full ap_pre n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
|--
  “ (n >= 0) ”
  &&  “ ((-1) <= n) ”
  &&  “ (n < n_pre) ”
  &&  “ ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) ”
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = val1) ”
  &&  “ ((last (l1) (1)) >= 1) ”
  &&  “ (list_within_bound UINT_MOD l1 ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = val2) ”
  &&  “ ((last (l2) (1)) >= 1) ”
  &&  “ (list_within_bound UINT_MOD l2 ) ”
  &&  (((bp_pre + (n * sizeof(UINT)))) # UInt  |-> (Znth n l2 0))
  **  (UIntArray.missing_i bp_pre n 0 n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
.

Definition mpn_cmp_partial_solve_wit_4 :=
forall (val2: Z) (val1: Z) (ap_pre: Z) (bp_pre: Z) (n_pre: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((Znth n l1 0) <> (Znth n l2 0))) (PreH2 : (n >= 0)) (PreH3 : ((-1) <= n)) (PreH4 : (n < n_pre)) (PreH5 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH6 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH7 : ((last (l1) (1)) >= 1)) (PreH8 : (list_within_bound UINT_MOD l1 )) (PreH9 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH10 : ((last (l2) (1)) >= 1)) (PreH11 : (list_within_bound UINT_MOD l2 )),
  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
|--
  “ ((Znth n l1 0) <> (Znth n l2 0)) ”
  &&  “ (n >= 0) ”
  &&  “ ((-1) <= n) ”
  &&  “ (n < n_pre) ”
  &&  “ ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) ”
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = val1) ”
  &&  “ ((last (l1) (1)) >= 1) ”
  &&  “ (list_within_bound UINT_MOD l1 ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = val2) ”
  &&  “ ((last (l2) (1)) >= 1) ”
  &&  “ (list_within_bound UINT_MOD l2 ) ”
  &&  (((ap_pre + (n * sizeof(UINT)))) # UInt  |-> (Znth n l1 0))
  **  (UIntArray.missing_i ap_pre n 0 n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
.

Definition mpn_cmp_partial_solve_wit_5 :=
forall (val2: Z) (val1: Z) (ap_pre: Z) (bp_pre: Z) (n_pre: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((Znth n l1 0) <> (Znth n l2 0))) (PreH2 : (n >= 0)) (PreH3 : ((-1) <= n)) (PreH4 : (n < n_pre)) (PreH5 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH6 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH7 : ((last (l1) (1)) >= 1)) (PreH8 : (list_within_bound UINT_MOD l1 )) (PreH9 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH10 : ((last (l2) (1)) >= 1)) (PreH11 : (list_within_bound UINT_MOD l2 )),
  (UIntArray.full ap_pre n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
|--
  “ ((Znth n l1 0) <> (Znth n l2 0)) ”
  &&  “ (n >= 0) ”
  &&  “ ((-1) <= n) ”
  &&  “ (n < n_pre) ”
  &&  “ ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) ”
  &&  “ ((list_to_Z (UINT_MOD) (l1)) = val1) ”
  &&  “ ((last (l1) (1)) >= 1) ”
  &&  “ (list_within_bound UINT_MOD l1 ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = val2) ”
  &&  “ ((last (l2) (1)) >= 1) ”
  &&  “ (list_within_bound UINT_MOD l2 ) ”
  &&  (((bp_pre + (n * sizeof(UINT)))) # UInt  |-> (Znth n l2 0))
  **  (UIntArray.missing_i bp_pre n 0 n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
.

Definition mpn_cmp_which_implies_wit_1 :=
(
forall (val2: Z) (val1: Z) (n: Z) (ap: Z) (bp: Z),
  (mpd_store_Z_compact UINT_MOD ap val1 n )
  **  (mpd_store_Z_compact UINT_MOD bp val2 n )
|--
  EX (l2: (@list Z)) (l1: (@list Z)),
  “ ((list_to_Z (UINT_MOD) (l1)) = val1) ”
  &&  “ ((last (l1) (1)) >= 1) ”
  &&  “ (list_within_bound UINT_MOD l1 ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = val2) ”
  &&  “ ((last (l2) (1)) >= 1) ”
  &&  “ (list_within_bound UINT_MOD l2 ) ”
  &&  “ (n = (Zlength (l1))) ”
  &&  “ (n = (Zlength (l2))) ”
  &&  (UIntArray.full ap n l1 )
  **  (UIntArray.full bp n l2 )
) \/
(
forall (val2: Z) (val1: Z) (n: Z) (ap: Z) (bp: Z),
  (mpd_store_Z_compact UINT_MOD ap val1 n )
  **  (mpd_store_Z_compact UINT_MOD bp val2 n )
|--
  EX (l2: (@list Z)) (l1: (@list Z)),
  “ ((list_to_Z (UINT_MOD) (l1)) = val1) ”
  &&  “ ((last (l1) (1)) >= 1) ”
  &&  “ (list_within_bound UINT_MOD l1 ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l2)) = val2) ”
  &&  “ ((last (l2) (1)) >= 1) ”
  &&  “ (list_within_bound UINT_MOD l2 ) ”
  &&  “ (n = (Zlength (l1))) ”
  &&  “ (n = (Zlength (l2))) ”
  &&  (UIntArray.full ap n l1 )
  **  (UIntArray.full bp n l2 )
).

(*----- Function mpn_cmp4 -----*)

Definition mpn_cmp4_safety_wit_1 :=
forall (val2: Z) (val1: Z) (ap_pre: Z) (an_pre: Z) (bp_pre: Z) (bn_pre: Z) (PreH1 : (an_pre < bn_pre)) (PreH2 : (an_pre <> bn_pre)) (PreH3 : (an_pre >= 0)) (PreH4 : (bn_pre >= 0)),
  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition mpn_cmp4_safety_wit_2 :=
forall (val2: Z) (val1: Z) (ap_pre: Z) (an_pre: Z) (bp_pre: Z) (bn_pre: Z) (PreH1 : (an_pre < bn_pre)) (PreH2 : (an_pre <> bn_pre)) (PreH3 : (an_pre >= 0)) (PreH4 : (bn_pre >= 0)),
  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_cmp4_safety_wit_3 :=
forall (val2: Z) (val1: Z) (ap_pre: Z) (an_pre: Z) (bp_pre: Z) (bn_pre: Z) (PreH1 : (an_pre >= bn_pre)) (PreH2 : (an_pre <> bn_pre)) (PreH3 : (an_pre >= 0)) (PreH4 : (bn_pre >= 0)),
  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_cmp4_return_wit_1 :=
(
forall (val2: Z) (val1: Z) (ap_pre: Z) (an_pre: Z) (bp_pre: Z) (bn_pre: Z) (retval: Z) (PreH1 : (val1 < val2)) (PreH2 : (retval = (-1))) (PreH3 : (an_pre = bn_pre)) (PreH4 : (an_pre >= 0)) (PreH5 : (bn_pre >= 0)),
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 an_pre )
|--
  “ (val1 < val2) ”
  &&  “ (retval = (-1)) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
) \/
(
forall (val2: Z) (val1: Z) (ap_pre: Z) (an_pre: Z) (bp_pre: Z) (bn_pre: Z) (retval: Z) (PreH1 : (val1 < val2)) (PreH2 : (retval = (-1))) (PreH3 : (an_pre = bn_pre)) (PreH4 : (an_pre >= 0)) (PreH5 : (bn_pre >= 0)),
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 an_pre )
|--
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
).

Definition mpn_cmp4_return_wit_1_split_goal_spatial :=
forall (val2: Z) (val1: Z) (ap_pre: Z) (an_pre: Z) (bp_pre: Z) (bn_pre: Z) (retval: Z) (PreH1 : (val1 < val2)) (PreH2 : (retval = (-1))) (PreH3 : (an_pre = bn_pre)) (PreH4 : (an_pre >= 0)) (PreH5 : (bn_pre >= 0)),
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 an_pre )
|--
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
.

Definition mpn_cmp4_return_wit_2 :=
(
forall (val2: Z) (val1: Z) (ap_pre: Z) (an_pre: Z) (bp_pre: Z) (bn_pre: Z) (retval: Z) (PreH1 : (val1 = val2)) (PreH2 : (retval = 0)) (PreH3 : (an_pre = bn_pre)) (PreH4 : (an_pre >= 0)) (PreH5 : (bn_pre >= 0)),
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 an_pre )
|--
  “ (val1 = val2) ”
  &&  “ (retval = 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
) \/
(
forall (val2: Z) (val1: Z) (ap_pre: Z) (an_pre: Z) (bp_pre: Z) (bn_pre: Z) (retval: Z) (PreH1 : (val1 = val2)) (PreH2 : (retval = 0)) (PreH3 : (an_pre = bn_pre)) (PreH4 : (an_pre >= 0)) (PreH5 : (bn_pre >= 0)),
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 an_pre )
|--
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
).

Definition mpn_cmp4_return_wit_2_split_goal_spatial :=
forall (val2: Z) (val1: Z) (ap_pre: Z) (an_pre: Z) (bp_pre: Z) (bn_pre: Z) (retval: Z) (PreH1 : (val1 = val2)) (PreH2 : (retval = 0)) (PreH3 : (an_pre = bn_pre)) (PreH4 : (an_pre >= 0)) (PreH5 : (bn_pre >= 0)),
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 an_pre )
|--
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
.

Definition mpn_cmp4_return_wit_3 :=
(
forall (val2: Z) (val1: Z) (ap_pre: Z) (an_pre: Z) (bp_pre: Z) (bn_pre: Z) (retval: Z) (PreH1 : (val1 > val2)) (PreH2 : (retval = 1)) (PreH3 : (an_pre = bn_pre)) (PreH4 : (an_pre >= 0)) (PreH5 : (bn_pre >= 0)),
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 an_pre )
|--
  “ (val1 > val2) ”
  &&  “ (retval = 1) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
) \/
(
forall (val2: Z) (val1: Z) (ap_pre: Z) (an_pre: Z) (bp_pre: Z) (bn_pre: Z) (retval: Z) (PreH1 : (val1 > val2)) (PreH2 : (retval = 1)) (PreH3 : (an_pre = bn_pre)) (PreH4 : (an_pre >= 0)) (PreH5 : (bn_pre >= 0)),
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 an_pre )
|--
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
).

Definition mpn_cmp4_return_wit_3_split_goal_spatial :=
forall (val2: Z) (val1: Z) (ap_pre: Z) (an_pre: Z) (bp_pre: Z) (bn_pre: Z) (retval: Z) (PreH1 : (val1 > val2)) (PreH2 : (retval = 1)) (PreH3 : (an_pre = bn_pre)) (PreH4 : (an_pre >= 0)) (PreH5 : (bn_pre >= 0)),
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 an_pre )
|--
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
.

Definition mpn_cmp4_return_wit_4 :=
(
forall (val2: Z) (val1: Z) (ap_pre: Z) (an_pre: Z) (bp_pre: Z) (bn_pre: Z) (PreH1 : (an_pre < bn_pre)) (PreH2 : (an_pre <> bn_pre)) (PreH3 : (an_pre >= 0)) (PreH4 : (bn_pre >= 0)),
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
|--
  “ (val1 < val2) ”
  &&  “ ((-1) = (-1)) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
) \/
(
forall (val2: Z) (val1: Z) (an_pre: Z) (bn_pre: Z) (PreH1 : (an_pre < bn_pre)) (PreH2 : (an_pre <> bn_pre)) (PreH3 : (an_pre >= 0)) (PreH4 : (bn_pre >= 0)),
  TT && emp 
|--
  “ (val1 < val2) ”
  &&  emp
).

Definition mpn_cmp4_return_wit_4_split_goal_1 :=
forall (val2: Z) (val1: Z) (an_pre: Z) (bn_pre: Z) (PreH1 : (an_pre < bn_pre)) (PreH2 : (an_pre <> bn_pre)) (PreH3 : (an_pre >= 0)) (PreH4 : (bn_pre >= 0)),
  (val1 < val2)
.

Definition mpn_cmp4_return_wit_5 :=
(
forall (val2: Z) (val1: Z) (ap_pre: Z) (an_pre: Z) (bp_pre: Z) (bn_pre: Z) (PreH1 : (an_pre >= bn_pre)) (PreH2 : (an_pre <> bn_pre)) (PreH3 : (an_pre >= 0)) (PreH4 : (bn_pre >= 0)),
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
|--
  “ (val1 > val2) ”
  &&  “ (1 = 1) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
) \/
(
forall (val2: Z) (val1: Z) (an_pre: Z) (bn_pre: Z) (PreH1 : (an_pre >= bn_pre)) (PreH2 : (an_pre <> bn_pre)) (PreH3 : (an_pre >= 0)) (PreH4 : (bn_pre >= 0)),
  TT && emp 
|--
  “ (val1 > val2) ”
  &&  emp
).

Definition mpn_cmp4_return_wit_5_split_goal_1 :=
forall (val2: Z) (val1: Z) (an_pre: Z) (bn_pre: Z) (PreH1 : (an_pre >= bn_pre)) (PreH2 : (an_pre <> bn_pre)) (PreH3 : (an_pre >= 0)) (PreH4 : (bn_pre >= 0)),
  (val1 > val2)
.

Definition mpn_cmp4_partial_solve_wit_1_pure :=
forall (val2: Z) (val1: Z) (ap_pre: Z) (an_pre: Z) (bp_pre: Z) (bn_pre: Z) (PreH1 : (an_pre = bn_pre)) (PreH2 : (an_pre >= 0)) (PreH3 : (bn_pre >= 0)),
  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
|--
  “ (0 <= an_pre) ”
.

Definition mpn_cmp4_partial_solve_wit_1_aux :=
forall (val2: Z) (val1: Z) (ap_pre: Z) (an_pre: Z) (bp_pre: Z) (bn_pre: Z) (PreH1 : (an_pre = bn_pre)) (PreH2 : (an_pre >= 0)) (PreH3 : (bn_pre >= 0)),
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
|--
  “ (0 <= an_pre) ”
  &&  “ (an_pre = bn_pre) ”
  &&  “ (an_pre >= 0) ”
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 an_pre )
.

Definition mpn_cmp4_partial_solve_wit_1 := mpn_cmp4_partial_solve_wit_1_pure -> mpn_cmp4_partial_solve_wit_1_aux.

(*----- Function gmp_umul_ppmm -----*)

Definition gmp_umul_ppmm_safety_wit_1 :=
forall (w0_pre: Z) (w1_pre: Z) (u_pre: Z) (v_pre: Z) (PreH1 : (0 <= v_pre)) (PreH2 : (v_pre <= UINT_MAX)) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre <= UINT_MAX)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (v_pre <= UINT_MAX)) (PreH7 : (u_pre >= 0)) (PreH8 : (v_pre >= 0)),
  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |->_)
  **  ((( &( "__uh" ) )) # UInt  |->_)
  **  ((( &( "__vl" ) )) # UInt  |->_)
  **  ((( &( "__ul" ) )) # UInt  |->_)
  **  ((( &( "__x3" ) )) # UInt  |->_)
  **  ((( &( "__x2" ) )) # UInt  |->_)
  **  ((( &( "__x1" ) )) # UInt  |->_)
  **  ((( &( "__x0" ) )) # UInt  |->_)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (65535 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 65535) ”
.

Definition gmp_umul_ppmm_safety_wit_2 :=
forall (w0_pre: Z) (w1_pre: Z) (u_pre: Z) (v_pre: Z) (PreH1 : (0 <= v_pre)) (PreH2 : (v_pre <= UINT_MAX)) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre <= UINT_MAX)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (v_pre <= UINT_MAX)) (PreH7 : (u_pre >= 0)) (PreH8 : (v_pre >= 0)),
  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |->_)
  **  ((( &( "__uh" ) )) # UInt  |->_)
  **  ((( &( "__vl" ) )) # UInt  |->_)
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |->_)
  **  ((( &( "__x2" ) )) # UInt  |->_)
  **  ((( &( "__x1" ) )) # UInt  |->_)
  **  ((( &( "__x0" ) )) # UInt  |->_)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (16 <= 31) ”
  &&  “ (0 <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_3 :=
forall (w0_pre: Z) (w1_pre: Z) (u_pre: Z) (v_pre: Z) (PreH1 : (0 <= v_pre)) (PreH2 : (v_pre <= UINT_MAX)) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre <= UINT_MAX)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (v_pre <= UINT_MAX)) (PreH7 : (u_pre >= 0)) (PreH8 : (v_pre >= 0)),
  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |->_)
  **  ((( &( "__uh" ) )) # UInt  |->_)
  **  ((( &( "__vl" ) )) # UInt  |->_)
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |->_)
  **  ((( &( "__x2" ) )) # UInt  |->_)
  **  ((( &( "__x1" ) )) # UInt  |->_)
  **  ((( &( "__x0" ) )) # UInt  |->_)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (16 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_4 :=
forall (w0_pre: Z) (w1_pre: Z) (u_pre: Z) (v_pre: Z) (PreH1 : (0 <= v_pre)) (PreH2 : (v_pre <= UINT_MAX)) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre <= UINT_MAX)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (v_pre <= UINT_MAX)) (PreH7 : (u_pre >= 0)) (PreH8 : (v_pre >= 0)),
  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |->_)
  **  ((( &( "__uh" ) )) # UInt  |-> (Z.shiftr u_pre 16))
  **  ((( &( "__vl" ) )) # UInt  |->_)
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |->_)
  **  ((( &( "__x2" ) )) # UInt  |->_)
  **  ((( &( "__x1" ) )) # UInt  |->_)
  **  ((( &( "__x0" ) )) # UInt  |->_)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (65535 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 65535) ”
.

Definition gmp_umul_ppmm_safety_wit_5 :=
forall (w0_pre: Z) (w1_pre: Z) (u_pre: Z) (v_pre: Z) (PreH1 : (0 <= v_pre)) (PreH2 : (v_pre <= UINT_MAX)) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre <= UINT_MAX)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (v_pre <= UINT_MAX)) (PreH7 : (u_pre >= 0)) (PreH8 : (v_pre >= 0)),
  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |->_)
  **  ((( &( "__uh" ) )) # UInt  |-> (Z.shiftr u_pre 16))
  **  ((( &( "__vl" ) )) # UInt  |-> (Z.land v_pre 65535))
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |->_)
  **  ((( &( "__x2" ) )) # UInt  |->_)
  **  ((( &( "__x1" ) )) # UInt  |->_)
  **  ((( &( "__x0" ) )) # UInt  |->_)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (16 <= 31) ”
  &&  “ (0 <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_6 :=
forall (w0_pre: Z) (w1_pre: Z) (u_pre: Z) (v_pre: Z) (PreH1 : (0 <= v_pre)) (PreH2 : (v_pre <= UINT_MAX)) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre <= UINT_MAX)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (v_pre <= UINT_MAX)) (PreH7 : (u_pre >= 0)) (PreH8 : (v_pre >= 0)),
  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |->_)
  **  ((( &( "__uh" ) )) # UInt  |-> (Z.shiftr u_pre 16))
  **  ((( &( "__vl" ) )) # UInt  |-> (Z.land v_pre 65535))
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |->_)
  **  ((( &( "__x2" ) )) # UInt  |->_)
  **  ((( &( "__x1" ) )) # UInt  |->_)
  **  ((( &( "__x0" ) )) # UInt  |->_)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (16 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_7 :=
forall (w0_pre: Z) (w1_pre: Z) (u_pre: Z) (v_pre: Z) (PreH1 : (0 <= v_pre)) (PreH2 : (v_pre <= UINT_MAX)) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre <= UINT_MAX)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (v_pre <= UINT_MAX)) (PreH7 : (u_pre >= 0)) (PreH8 : (v_pre >= 0)),
  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |-> (Z.shiftr v_pre 16))
  **  ((( &( "__uh" ) )) # UInt  |-> (Z.shiftr u_pre 16))
  **  ((( &( "__vl" ) )) # UInt  |-> (Z.land v_pre 65535))
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)))
  **  ((( &( "__x2" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "__x1" ) )) # UInt  |-> (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)))
  **  ((( &( "__x0" ) )) # UInt  |-> (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (16 <= 31) ”
  &&  “ (0 <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_8 :=
forall (w0_pre: Z) (w1_pre: Z) (u_pre: Z) (v_pre: Z) (PreH1 : (0 <= v_pre)) (PreH2 : (v_pre <= UINT_MAX)) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre <= UINT_MAX)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (v_pre <= UINT_MAX)) (PreH7 : (u_pre >= 0)) (PreH8 : (v_pre >= 0)),
  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |-> (Z.shiftr v_pre 16))
  **  ((( &( "__uh" ) )) # UInt  |-> (Z.shiftr u_pre 16))
  **  ((( &( "__vl" ) )) # UInt  |-> (Z.land v_pre 65535))
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)))
  **  ((( &( "__x2" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "__x1" ) )) # UInt  |-> (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)))
  **  ((( &( "__x0" ) )) # UInt  |-> (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (16 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_9 :=
forall (w0_pre: Z) (w1_pre: Z) (u_pre: Z) (v_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) < (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= UINT_MAX)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (u_pre >= 0)) (PreH9 : (v_pre >= 0)),
  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |-> (Z.shiftr v_pre 16))
  **  ((( &( "__uh" ) )) # UInt  |-> (Z.shiftr u_pre 16))
  **  ((( &( "__vl" ) )) # UInt  |-> (Z.land v_pre 65535))
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)))
  **  ((( &( "__x2" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "__x1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)))
  **  ((( &( "__x0" ) )) # UInt  |-> (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (65536 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 65536) ”
.

Definition gmp_umul_ppmm_safety_wit_10 :=
forall (w0_pre: Z) (w1_pre: Z) (u_pre: Z) (v_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) < (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= UINT_MAX)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (u_pre >= 0)) (PreH9 : (v_pre >= 0)),
  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |-> (Z.shiftr v_pre 16))
  **  ((( &( "__uh" ) )) # UInt  |-> (Z.shiftr u_pre 16))
  **  ((( &( "__vl" ) )) # UInt  |-> (Z.land v_pre 65535))
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + 65536 )) (32)))
  **  ((( &( "__x2" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "__x1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)))
  **  ((( &( "__x0" ) )) # UInt  |-> (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (16 <= 31) ”
  &&  “ (0 <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_11 :=
forall (w0_pre: Z) (w1_pre: Z) (u_pre: Z) (v_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) < (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= UINT_MAX)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (u_pre >= 0)) (PreH9 : (v_pre >= 0)),
  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |-> (Z.shiftr v_pre 16))
  **  ((( &( "__uh" ) )) # UInt  |-> (Z.shiftr u_pre 16))
  **  ((( &( "__vl" ) )) # UInt  |-> (Z.land v_pre 65535))
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + 65536 )) (32)))
  **  ((( &( "__x2" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "__x1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)))
  **  ((( &( "__x0" ) )) # UInt  |-> (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (16 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_12 :=
forall (w0_pre: Z) (w1_pre: Z) (u_pre: Z) (v_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) >= (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= UINT_MAX)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (u_pre >= 0)) (PreH9 : (v_pre >= 0)),
  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |-> (Z.shiftr v_pre 16))
  **  ((( &( "__uh" ) )) # UInt  |-> (Z.shiftr u_pre 16))
  **  ((( &( "__vl" ) )) # UInt  |-> (Z.land v_pre 65535))
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)))
  **  ((( &( "__x2" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "__x1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)))
  **  ((( &( "__x0" ) )) # UInt  |-> (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (16 <= 31) ”
  &&  “ (0 <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_13 :=
forall (w0_pre: Z) (w1_pre: Z) (u_pre: Z) (v_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) >= (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= UINT_MAX)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (u_pre >= 0)) (PreH9 : (v_pre >= 0)),
  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |-> (Z.shiftr v_pre 16))
  **  ((( &( "__uh" ) )) # UInt  |-> (Z.shiftr u_pre 16))
  **  ((( &( "__vl" ) )) # UInt  |-> (Z.land v_pre 65535))
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)))
  **  ((( &( "__x2" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "__x1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)))
  **  ((( &( "__x0" ) )) # UInt  |-> (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (16 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_14 :=
forall (w0_pre: Z) (w1_pre: Z) (u_pre: Z) (v_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) < (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= UINT_MAX)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (u_pre >= 0)) (PreH9 : (v_pre >= 0)),
  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |-> (Z.shiftr v_pre 16))
  **  ((( &( "__uh" ) )) # UInt  |-> (Z.shiftr u_pre 16))
  **  ((( &( "__vl" ) )) # UInt  |-> (Z.land v_pre 65535))
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + 65536 )) (32)))
  **  ((( &( "__x2" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "__x1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)))
  **  ((( &( "__x0" ) )) # UInt  |-> (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + 65536 )) (32)) + (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16) )) (32)))
|--
  “ (16 <= 31) ”
  &&  “ (0 <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_15 :=
forall (w0_pre: Z) (w1_pre: Z) (u_pre: Z) (v_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) < (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= UINT_MAX)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (u_pre >= 0)) (PreH9 : (v_pre >= 0)),
  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |-> (Z.shiftr v_pre 16))
  **  ((( &( "__uh" ) )) # UInt  |-> (Z.shiftr u_pre 16))
  **  ((( &( "__vl" ) )) # UInt  |-> (Z.land v_pre 65535))
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + 65536 )) (32)))
  **  ((( &( "__x2" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "__x1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)))
  **  ((( &( "__x0" ) )) # UInt  |-> (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + 65536 )) (32)) + (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16) )) (32)))
|--
  “ (16 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_16 :=
forall (w0_pre: Z) (w1_pre: Z) (u_pre: Z) (v_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) < (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= UINT_MAX)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (u_pre >= 0)) (PreH9 : (v_pre >= 0)),
  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |-> (Z.shiftr v_pre 16))
  **  ((( &( "__uh" ) )) # UInt  |-> (Z.shiftr u_pre 16))
  **  ((( &( "__vl" ) )) # UInt  |-> (Z.land v_pre 65535))
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + 65536 )) (32)))
  **  ((( &( "__x2" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "__x1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)))
  **  ((( &( "__x0" ) )) # UInt  |-> (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + 65536 )) (32)) + (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16) )) (32)))
|--
  “ (65535 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 65535) ”
.

Definition gmp_umul_ppmm_safety_wit_17 :=
forall (w0_pre: Z) (w1_pre: Z) (u_pre: Z) (v_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) >= (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= UINT_MAX)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (u_pre >= 0)) (PreH9 : (v_pre >= 0)),
  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |-> (Z.shiftr v_pre 16))
  **  ((( &( "__uh" ) )) # UInt  |-> (Z.shiftr u_pre 16))
  **  ((( &( "__vl" ) )) # UInt  |-> (Z.land v_pre 65535))
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)))
  **  ((( &( "__x2" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "__x1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)))
  **  ((( &( "__x0" ) )) # UInt  |-> (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16) )) (32)))
|--
  “ (16 <= 31) ”
  &&  “ (0 <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_18 :=
forall (w0_pre: Z) (w1_pre: Z) (u_pre: Z) (v_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) >= (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= UINT_MAX)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (u_pre >= 0)) (PreH9 : (v_pre >= 0)),
  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |-> (Z.shiftr v_pre 16))
  **  ((( &( "__uh" ) )) # UInt  |-> (Z.shiftr u_pre 16))
  **  ((( &( "__vl" ) )) # UInt  |-> (Z.land v_pre 65535))
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)))
  **  ((( &( "__x2" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "__x1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)))
  **  ((( &( "__x0" ) )) # UInt  |-> (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16) )) (32)))
|--
  “ (16 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_19 :=
forall (w0_pre: Z) (w1_pre: Z) (u_pre: Z) (v_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) >= (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= UINT_MAX)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (u_pre >= 0)) (PreH9 : (v_pre >= 0)),
  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |-> (Z.shiftr v_pre 16))
  **  ((( &( "__uh" ) )) # UInt  |-> (Z.shiftr u_pre 16))
  **  ((( &( "__vl" ) )) # UInt  |-> (Z.land v_pre 65535))
  **  ((( &( "__ul" ) )) # UInt  |-> (Z.land u_pre 65535))
  **  ((( &( "__x3" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)))
  **  ((( &( "__x2" ) )) # UInt  |-> (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "__x1" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)))
  **  ((( &( "__x0" ) )) # UInt  |-> (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)))
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16) )) (32)))
|--
  “ (65535 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 65535) ”
.

Definition gmp_umul_ppmm_entail_wit_1 :=
forall (w0_pre: Z) (w1_pre: Z) (u_pre: Z) (v_pre: Z),
  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |->_)
  **  ((( &( "__uh" ) )) # UInt  |->_)
  **  ((( &( "__vl" ) )) # UInt  |->_)
  **  ((( &( "__ul" ) )) # UInt  |->_)
  **  ((( &( "__x3" ) )) # UInt  |->_)
  **  ((( &( "__x2" ) )) # UInt  |->_)
  **  ((( &( "__x1" ) )) # UInt  |->_)
  **  ((( &( "__x0" ) )) # UInt  |->_)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (0 <= u_pre) ”
  &&  “ (u_pre <= UINT_MAX) ”
  &&  “ (u_pre <= UINT_MAX) ”
  &&  “ (v_pre <= UINT_MAX) ”
  &&  “ (u_pre >= 0) ”
  &&  “ (v_pre >= 0) ”
  &&  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |->_)
  **  ((( &( "__uh" ) )) # UInt  |->_)
  **  ((( &( "__vl" ) )) # UInt  |->_)
  **  ((( &( "__ul" ) )) # UInt  |->_)
  **  ((( &( "__x3" ) )) # UInt  |->_)
  **  ((( &( "__x2" ) )) # UInt  |->_)
  **  ((( &( "__x1" ) )) # UInt  |->_)
  **  ((( &( "__x0" ) )) # UInt  |->_)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
.

Definition gmp_umul_ppmm_entail_wit_2 :=
forall (w0_pre: Z) (w1_pre: Z) (u_pre: Z) (v_pre: Z) (PreH1 : (0 <= u_pre)) (PreH2 : (u_pre <= UINT_MAX)) (PreH3 : (u_pre <= UINT_MAX)) (PreH4 : (v_pre <= UINT_MAX)) (PreH5 : (u_pre >= 0)) (PreH6 : (v_pre >= 0)),
  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |->_)
  **  ((( &( "__uh" ) )) # UInt  |->_)
  **  ((( &( "__vl" ) )) # UInt  |->_)
  **  ((( &( "__ul" ) )) # UInt  |->_)
  **  ((( &( "__x3" ) )) # UInt  |->_)
  **  ((( &( "__x2" ) )) # UInt  |->_)
  **  ((( &( "__x1" ) )) # UInt  |->_)
  **  ((( &( "__x0" ) )) # UInt  |->_)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (0 <= v_pre) ”
  &&  “ (v_pre <= UINT_MAX) ”
  &&  “ (0 <= u_pre) ”
  &&  “ (u_pre <= UINT_MAX) ”
  &&  “ (u_pre <= UINT_MAX) ”
  &&  “ (v_pre <= UINT_MAX) ”
  &&  “ (u_pre >= 0) ”
  &&  “ (v_pre >= 0) ”
  &&  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__v" ) )) # UInt  |-> v_pre)
  **  ((( &( "__u" ) )) # UInt  |-> u_pre)
  **  ((( &( "__vh" ) )) # UInt  |->_)
  **  ((( &( "__uh" ) )) # UInt  |->_)
  **  ((( &( "__vl" ) )) # UInt  |->_)
  **  ((( &( "__ul" ) )) # UInt  |->_)
  **  ((( &( "__x3" ) )) # UInt  |->_)
  **  ((( &( "__x2" ) )) # UInt  |->_)
  **  ((( &( "__x1" ) )) # UInt  |->_)
  **  ((( &( "__x0" ) )) # UInt  |->_)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
.

Definition gmp_umul_ppmm_return_wit_1 :=
(
forall (w0_pre: Z) (w1_pre: Z) (u_pre: Z) (v_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) < (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= UINT_MAX)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (u_pre >= 0)) (PreH9 : (v_pre >= 0)),
  ((w0_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16)) (32)) + (Z.land ((Z.land u_pre 65535) * (Z.land v_pre 65535) ) 65535) )) (32)))
  **  ((w1_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + 65536 )) (32)) + (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16) )) (32)))
|--
  EX (w0_value: Z) (w1_value: Z),
  “ (((w1_value * UINT_MOD ) + w0_value ) = (u_pre * v_pre )) ”
  &&  ((w0_pre) # UInt  |-> w0_value)
  **  ((w1_pre) # UInt  |-> w1_value)
) \/
(
forall (u_pre: Z) (v_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) < (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= UINT_MAX)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (u_pre >= 0)) (PreH9 : (v_pre >= 0)),
  TT && emp 
|--
  “ ((((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + 65536 )) (32)) + (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16) )) (32)) * UINT_MOD ) + (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16)) (32)) + (Z.land ((Z.land u_pre 65535) * (Z.land v_pre 65535) ) 65535) )) (32)) ) = (u_pre * v_pre )) ”
  &&  emp
).

Definition gmp_umul_ppmm_return_wit_1_split_goal_1 :=
forall (u_pre: Z) (v_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) < (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= UINT_MAX)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (u_pre >= 0)) (PreH9 : (v_pre >= 0)),
  ((((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + 65536 )) (32)) + (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16) )) (32)) * UINT_MOD ) + (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16)) (32)) + (Z.land ((Z.land u_pre 65535) * (Z.land v_pre 65535) ) 65535) )) (32)) ) = (u_pre * v_pre ))
.

Definition gmp_umul_ppmm_return_wit_2 :=
(
forall (w0_pre: Z) (w1_pre: Z) (u_pre: Z) (v_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) >= (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= UINT_MAX)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (u_pre >= 0)) (PreH9 : (v_pre >= 0)),
  ((w0_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16)) (32)) + (Z.land ((Z.land u_pre 65535) * (Z.land v_pre 65535) ) 65535) )) (32)))
  **  ((w1_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16) )) (32)))
|--
  EX (w0_value: Z) (w1_value: Z),
  “ (((w1_value * UINT_MOD ) + w0_value ) = (u_pre * v_pre )) ”
  &&  ((w0_pre) # UInt  |-> w0_value)
  **  ((w1_pre) # UInt  |-> w1_value)
) \/
(
forall (u_pre: Z) (v_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) >= (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= UINT_MAX)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (u_pre >= 0)) (PreH9 : (v_pre >= 0)),
  TT && emp 
|--
  “ ((((unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16) )) (32)) * UINT_MOD ) + (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16)) (32)) + (Z.land ((Z.land u_pre 65535) * (Z.land v_pre 65535) ) 65535) )) (32)) ) = (u_pre * v_pre )) ”
  &&  emp
).

Definition gmp_umul_ppmm_return_wit_2_split_goal_1 :=
forall (u_pre: Z) (v_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) >= (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= UINT_MAX)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (u_pre >= 0)) (PreH9 : (v_pre >= 0)),
  ((((unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16) )) (32)) * UINT_MOD ) + (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16)) (32)) + (Z.land ((Z.land u_pre 65535) * (Z.land v_pre 65535) ) 65535) )) (32)) ) = (u_pre * v_pre ))
.

(*----- Function mpn_mul_1 -----*)

Definition mpn_mul_1_safety_wit_1 :=
forall (l: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (vl_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (list_within_bound UINT_MOD l )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "lpl" ) )) # UInt  |->_)
  **  ((( &( "hpl" ) )) # UInt  |->_)
  **  ((( &( "cl" ) )) # UInt  |->_)
  **  ((( &( "ul" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_mul_1_safety_wit_2 :=
forall (l: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (vl_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (list_within_bound UINT_MOD l )),
  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "lpl" ) )) # UInt  |->_)
  **  ((( &( "hpl" ) )) # UInt  |->_)
  **  ((( &( "cl" ) )) # UInt  |->_)
  **  ((( &( "ul" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_mul_1_safety_wit_3 :=
forall (l: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (vl_pre: Z) (l_rp: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits ((lpl + cl )) (32)) >= cl)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= cl)) (PreH5 : (cl <= UINT_MAX)) (PreH6 : (0 <= lpl)) (PreH7 : (lpl <= UINT_MAX)) (PreH8 : (0 <= hpl)) (PreH9 : (hpl <= UINT_MAX)) (PreH10 : (list_within_bound UINT_MOD l_rp )) (PreH11 : (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))) (PreH12 : (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre ))) (PreH13 : (n_pre > 0)) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (0 <= vl_pre)) (PreH16 : (vl_pre <= UINT_MAX)) (PreH17 : (list_within_bound UINT_MOD l )),
  (UIntArray.seg rp_pre 0 (i + 1 ) (app (l_rp) ((cons ((unsigned_last_nbits ((lpl + cl )) (32))) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # UInt  |-> (0 + hpl ))
  **  ((( &( "lpl" ) )) # UInt  |-> (unsigned_last_nbits ((lpl + cl )) (32)))
  **  ((( &( "hpl" ) )) # UInt  |-> hpl)
  **  ((( &( "ul" ) )) # UInt  |-> (Znth i l 0))
  **  (UIntArray.full up_pre n_pre l )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_mul_1_safety_wit_4 :=
forall (l: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (vl_pre: Z) (l_rp: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits ((lpl + cl )) (32)) >= cl)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= cl)) (PreH5 : (cl <= UINT_MAX)) (PreH6 : (0 <= lpl)) (PreH7 : (lpl <= UINT_MAX)) (PreH8 : (0 <= hpl)) (PreH9 : (hpl <= UINT_MAX)) (PreH10 : (list_within_bound UINT_MOD l_rp )) (PreH11 : (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))) (PreH12 : (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre ))) (PreH13 : (n_pre > 0)) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (0 <= vl_pre)) (PreH16 : (vl_pre <= UINT_MAX)) (PreH17 : (list_within_bound UINT_MOD l )),
  (UIntArray.seg rp_pre 0 (i + 1 ) (app (l_rp) ((cons ((unsigned_last_nbits ((lpl + cl )) (32))) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # UInt  |-> (0 + hpl ))
  **  ((( &( "lpl" ) )) # UInt  |-> (unsigned_last_nbits ((lpl + cl )) (32)))
  **  ((( &( "hpl" ) )) # UInt  |-> hpl)
  **  ((( &( "ul" ) )) # UInt  |-> (Znth i l 0))
  **  (UIntArray.full up_pre n_pre l )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_mul_1_safety_wit_5 :=
forall (l: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (vl_pre: Z) (l_rp: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits ((lpl + cl )) (32)) < cl)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= cl)) (PreH5 : (cl <= UINT_MAX)) (PreH6 : (0 <= lpl)) (PreH7 : (lpl <= UINT_MAX)) (PreH8 : (0 <= hpl)) (PreH9 : (hpl <= UINT_MAX)) (PreH10 : (list_within_bound UINT_MOD l_rp )) (PreH11 : (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))) (PreH12 : (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre ))) (PreH13 : (n_pre > 0)) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (0 <= vl_pre)) (PreH16 : (vl_pre <= UINT_MAX)) (PreH17 : (list_within_bound UINT_MOD l )),
  (UIntArray.seg rp_pre 0 (i + 1 ) (app (l_rp) ((cons ((unsigned_last_nbits ((lpl + cl )) (32))) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # UInt  |-> (unsigned_last_nbits ((1 + hpl )) (32)))
  **  ((( &( "lpl" ) )) # UInt  |-> (unsigned_last_nbits ((lpl + cl )) (32)))
  **  ((( &( "hpl" ) )) # UInt  |-> hpl)
  **  ((( &( "ul" ) )) # UInt  |-> (Znth i l 0))
  **  (UIntArray.full up_pre n_pre l )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_mul_1_safety_wit_6 :=
forall (l: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (vl_pre: Z) (l_rp: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits ((lpl + cl )) (32)) < cl)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= cl)) (PreH5 : (cl <= UINT_MAX)) (PreH6 : (0 <= lpl)) (PreH7 : (lpl <= UINT_MAX)) (PreH8 : (0 <= hpl)) (PreH9 : (hpl <= UINT_MAX)) (PreH10 : (list_within_bound UINT_MOD l_rp )) (PreH11 : (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))) (PreH12 : (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre ))) (PreH13 : (n_pre > 0)) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (0 <= vl_pre)) (PreH16 : (vl_pre <= UINT_MAX)) (PreH17 : (list_within_bound UINT_MOD l )),
  (UIntArray.seg rp_pre 0 (i + 1 ) (app (l_rp) ((cons ((unsigned_last_nbits ((lpl + cl )) (32))) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # UInt  |-> (unsigned_last_nbits ((1 + hpl )) (32)))
  **  ((( &( "lpl" ) )) # UInt  |-> (unsigned_last_nbits ((lpl + cl )) (32)))
  **  ((( &( "hpl" ) )) # UInt  |-> hpl)
  **  ((( &( "ul" ) )) # UInt  |-> (Znth i l 0))
  **  (UIntArray.full up_pre n_pre l )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_mul_1_entail_wit_1 :=
(
forall (l: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (vl_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (list_within_bound UINT_MOD l )),
  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  EX (l_rp: (@list Z)),
  “ (0 < n_pre) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (0 <= vl_pre) ”
  &&  “ (vl_pre <= UINT_MAX) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= UINT_MAX) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ (list_within_bound UINT_MOD l_rp ) ”
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + (0 * (Z.pow (UINT_MOD) (0)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (0) (l)))) * vl_pre )) ”
  &&  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 0 l_rp )
  **  (UIntArray.undef_seg rp_pre 0 n_pre )
) \/
(
forall (l: (@list Z)) (n_pre: Z) (vl_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (list_within_bound UINT_MOD l )),
  TT && emp 
|--
  “ (((list_to_Z (UINT_MOD) ((@nil Z))) + (0 * (Z.pow (UINT_MOD) (0)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (0) (l)))) * vl_pre )) ”
  &&  “ (list_within_bound UINT_MOD (@nil Z) ) ”
  &&  emp
).

Definition mpn_mul_1_entail_wit_1_split_goal_1 :=
forall (l: (@list Z)) (n_pre: Z) (vl_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (list_within_bound UINT_MOD l )),
  (((list_to_Z (UINT_MOD) ((@nil Z))) + (0 * (Z.pow (UINT_MOD) (0)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (0) (l)))) * vl_pre ))
.

Definition mpn_mul_1_entail_wit_1_split_goal_2 :=
forall (l: (@list Z)) (n_pre: Z) (vl_pre: Z) (PreH1 : (n_pre > 0)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (list_within_bound UINT_MOD l )),
  (list_within_bound UINT_MOD (@nil Z) )
.

Definition mpn_mul_1_entail_wit_2 :=
forall (l: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (vl_pre: Z) (l_rp: (@list Z)) (cl: Z) (i: Z) (w0_value: Z) (w1_value: Z) (PreH1 : (((w1_value * UINT_MOD ) + w0_value ) = ((Znth i l 0) * vl_pre ))) (PreH2 : (i < n_pre)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (0 <= vl_pre)) (PreH6 : (vl_pre <= UINT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= cl)) (PreH10 : (cl <= UINT_MAX)) (PreH11 : (list_within_bound UINT_MOD l )) (PreH12 : (list_within_bound UINT_MOD l_rp )) (PreH13 : (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))),
  ((( &( "lpl" ) )) # UInt  |-> w0_value)
  **  ((( &( "hpl" ) )) # UInt  |-> w1_value)
  **  (UIntArray.full up_pre n_pre l )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # UInt  |-> cl)
  **  ((( &( "ul" ) )) # UInt  |-> (Znth i l 0))
  **  (UIntArray.seg rp_pre 0 i l_rp )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ (0 <= w0_value) ”
  &&  “ (w0_value <= UINT_MAX) ”
  &&  “ ((Znth i l 0) <= UINT_MAX) ”
  &&  “ (w1_value <= UINT_MAX) ”
  &&  “ ((Znth i l 0) >= 0) ”
  &&  “ (cl >= 0) ”
  &&  “ (vl_pre >= 0) ”
  &&  “ (w1_value >= 0) ”
  &&  “ (i <= INT_MAX) ”
  &&  “ (i >= INT_MIN) ”
  &&  “ (n_pre >= INT_MIN) ”
  &&  “ (((w1_value * UINT_MOD ) + w0_value ) = ((Znth i l 0) * vl_pre )) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 < n_pre) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (0 <= vl_pre) ”
  &&  “ (vl_pre <= UINT_MAX) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= cl) ”
  &&  “ (cl <= UINT_MAX) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ (list_within_bound UINT_MOD l_rp ) ”
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre )) ”
  &&  ((( &( "lpl" ) )) # UInt  |-> w0_value)
  **  ((( &( "hpl" ) )) # UInt  |-> w1_value)
  **  (UIntArray.full up_pre n_pre l )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # UInt  |-> cl)
  **  ((( &( "ul" ) )) # UInt  |-> (Znth i l 0))
  **  (UIntArray.seg rp_pre 0 i l_rp )
  **  (UIntArray.undef_seg rp_pre i n_pre )
.

Definition mpn_mul_1_entail_wit_3 :=
forall (l: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (vl_pre: Z) (l_rp: (@list Z)) (cl: Z) (i: Z) (w0_value: Z) (w1_value: Z) (PreH1 : (0 <= w0_value)) (PreH2 : (w0_value <= UINT_MAX)) (PreH3 : ((Znth i l 0) <= UINT_MAX)) (PreH4 : (w1_value <= UINT_MAX)) (PreH5 : ((Znth i l 0) >= 0)) (PreH6 : (cl >= 0)) (PreH7 : (vl_pre >= 0)) (PreH8 : (w1_value >= 0)) (PreH9 : (i <= INT_MAX)) (PreH10 : (i >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (((w1_value * UINT_MOD ) + w0_value ) = ((Znth i l 0) * vl_pre ))) (PreH13 : (i < n_pre)) (PreH14 : (0 < n_pre)) (PreH15 : (n_pre <= INT_MAX)) (PreH16 : (0 <= vl_pre)) (PreH17 : (vl_pre <= UINT_MAX)) (PreH18 : (0 <= i)) (PreH19 : (i <= n_pre)) (PreH20 : (0 <= cl)) (PreH21 : (cl <= UINT_MAX)) (PreH22 : (list_within_bound UINT_MOD l )) (PreH23 : (list_within_bound UINT_MOD l_rp )) (PreH24 : (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))),
  ((( &( "lpl" ) )) # UInt  |-> w0_value)
  **  ((( &( "hpl" ) )) # UInt  |-> w1_value)
  **  (UIntArray.full up_pre n_pre l )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # UInt  |-> cl)
  **  ((( &( "ul" ) )) # UInt  |-> (Znth i l 0))
  **  (UIntArray.seg rp_pre 0 i l_rp )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ (0 <= w1_value) ”
  &&  “ (w1_value <= UINT_MAX) ”
  &&  “ (w0_value >= 0) ”
  &&  “ (0 <= w0_value) ”
  &&  “ (w0_value <= UINT_MAX) ”
  &&  “ ((Znth i l 0) <= UINT_MAX) ”
  &&  “ (w1_value <= UINT_MAX) ”
  &&  “ ((Znth i l 0) >= 0) ”
  &&  “ (cl >= 0) ”
  &&  “ (vl_pre >= 0) ”
  &&  “ (w1_value >= 0) ”
  &&  “ (i <= INT_MAX) ”
  &&  “ (i >= INT_MIN) ”
  &&  “ (n_pre >= INT_MIN) ”
  &&  “ (((w1_value * UINT_MOD ) + w0_value ) = ((Znth i l 0) * vl_pre )) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 < n_pre) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (0 <= vl_pre) ”
  &&  “ (vl_pre <= UINT_MAX) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= cl) ”
  &&  “ (cl <= UINT_MAX) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ (list_within_bound UINT_MOD l_rp ) ”
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre )) ”
  &&  ((( &( "hpl" ) )) # UInt  |-> w1_value)
  **  ((( &( "lpl" ) )) # UInt  |-> w0_value)
  **  (UIntArray.full up_pre n_pre l )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # UInt  |-> cl)
  **  ((( &( "ul" ) )) # UInt  |-> (Znth i l 0))
  **  (UIntArray.seg rp_pre 0 i l_rp )
  **  (UIntArray.undef_seg rp_pre i n_pre )
.

Definition mpn_mul_1_entail_wit_4 :=
forall (l: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (vl_pre: Z) (l_rp_2: (@list Z)) (cl: Z) (i: Z) (w0_value: Z) (w1_value: Z) (PreH1 : (0 <= w1_value)) (PreH2 : (w1_value <= UINT_MAX)) (PreH3 : (w0_value >= 0)) (PreH4 : (0 <= w0_value)) (PreH5 : (w0_value <= UINT_MAX)) (PreH6 : ((Znth i l 0) <= UINT_MAX)) (PreH7 : (w1_value <= UINT_MAX)) (PreH8 : ((Znth i l 0) >= 0)) (PreH9 : (cl >= 0)) (PreH10 : (vl_pre >= 0)) (PreH11 : (w1_value >= 0)) (PreH12 : (i <= INT_MAX)) (PreH13 : (i >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (((w1_value * UINT_MOD ) + w0_value ) = ((Znth i l 0) * vl_pre ))) (PreH16 : (i < n_pre)) (PreH17 : (0 < n_pre)) (PreH18 : (n_pre <= INT_MAX)) (PreH19 : (0 <= vl_pre)) (PreH20 : (vl_pre <= UINT_MAX)) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= cl)) (PreH24 : (cl <= UINT_MAX)) (PreH25 : (list_within_bound UINT_MOD l )) (PreH26 : (list_within_bound UINT_MOD l_rp_2 )) (PreH27 : (((list_to_Z (UINT_MOD) (l_rp_2)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))),
  (UIntArray.full up_pre n_pre l )
  **  ((( &( "ul" ) )) # UInt  |-> (Znth i l 0))
  **  (UIntArray.seg rp_pre 0 i l_rp_2 )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  EX (l_rp: (@list Z)),
  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= cl) ”
  &&  “ (cl <= UINT_MAX) ”
  &&  “ (0 <= w0_value) ”
  &&  “ (w0_value <= UINT_MAX) ”
  &&  “ (0 <= w1_value) ”
  &&  “ (w1_value <= UINT_MAX) ”
  &&  “ (list_within_bound UINT_MOD l_rp ) ”
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre )) ”
  &&  “ (((w1_value * UINT_MOD ) + w0_value ) = ((Znth i l 0) * vl_pre )) ”
  &&  “ (n_pre > 0) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (0 <= vl_pre) ”
  &&  “ (vl_pre <= UINT_MAX) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  ((( &( "ul" ) )) # UInt  |-> (Znth i l 0))
  **  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i l_rp )
  **  (UIntArray.undef_seg rp_pre i n_pre )
.

Definition mpn_mul_1_entail_wit_5_1 :=
(
forall (l: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (vl_pre: Z) (l_rp_2: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits ((lpl + cl )) (32)) >= cl)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= cl)) (PreH5 : (cl <= UINT_MAX)) (PreH6 : (0 <= lpl)) (PreH7 : (lpl <= UINT_MAX)) (PreH8 : (0 <= hpl)) (PreH9 : (hpl <= UINT_MAX)) (PreH10 : (list_within_bound UINT_MOD l_rp_2 )) (PreH11 : (((list_to_Z (UINT_MOD) (l_rp_2)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))) (PreH12 : (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre ))) (PreH13 : (n_pre > 0)) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (0 <= vl_pre)) (PreH16 : (vl_pre <= UINT_MAX)) (PreH17 : (list_within_bound UINT_MOD l )),
  (UIntArray.seg rp_pre 0 (i + 1 ) (app (l_rp_2) ((cons ((unsigned_last_nbits ((lpl + cl )) (32))) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  ((( &( "lpl" ) )) # UInt  |-> (unsigned_last_nbits ((lpl + cl )) (32)))
  **  ((( &( "hpl" ) )) # UInt  |-> hpl)
  **  ((( &( "ul" ) )) # UInt  |-> (Znth i l 0))
  **  (UIntArray.full up_pre n_pre l )
|--
  EX (l_rp: (@list Z)),
  “ (0 < n_pre) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (0 <= vl_pre) ”
  &&  “ (vl_pre <= UINT_MAX) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (0 <= (0 + hpl )) ”
  &&  “ ((0 + hpl ) <= UINT_MAX) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ (list_within_bound UINT_MOD l_rp ) ”
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + ((0 + hpl ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) * vl_pre )) ”
  &&  ((( &( "ul" ) )) # UInt  |->_)
  **  ((( &( "lpl" ) )) # UInt  |->_)
  **  ((( &( "hpl" ) )) # UInt  |->_)
  **  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 (i + 1 ) l_rp )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
) \/
(
forall (l: (@list Z)) (n_pre: Z) (vl_pre: Z) (l_rp_2: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits ((lpl + cl )) (32)) >= cl)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= cl)) (PreH5 : (cl <= UINT_MAX)) (PreH6 : (0 <= lpl)) (PreH7 : (lpl <= UINT_MAX)) (PreH8 : (0 <= hpl)) (PreH9 : (hpl <= UINT_MAX)) (PreH10 : (list_within_bound UINT_MOD l_rp_2 )) (PreH11 : (((list_to_Z (UINT_MOD) (l_rp_2)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))) (PreH12 : (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre ))) (PreH13 : (n_pre > 0)) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (0 <= vl_pre)) (PreH16 : (vl_pre <= UINT_MAX)) (PreH17 : (list_within_bound UINT_MOD l )),
  TT && emp 
|--
  “ (((list_to_Z (UINT_MOD) ((app (l_rp_2) ((cons ((unsigned_last_nbits ((lpl + cl )) (32))) ((@nil Z))))))) + ((0 + hpl ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) * vl_pre )) ”
  &&  “ (list_within_bound UINT_MOD (app (l_rp_2) ((cons ((unsigned_last_nbits ((lpl + cl )) (32))) ((@nil Z))))) ) ”
  &&  emp
).

Definition mpn_mul_1_entail_wit_5_1_split_goal_1 :=
forall (l: (@list Z)) (n_pre: Z) (vl_pre: Z) (l_rp_2: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits ((lpl + cl )) (32)) >= cl)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= cl)) (PreH5 : (cl <= UINT_MAX)) (PreH6 : (0 <= lpl)) (PreH7 : (lpl <= UINT_MAX)) (PreH8 : (0 <= hpl)) (PreH9 : (hpl <= UINT_MAX)) (PreH10 : (list_within_bound UINT_MOD l_rp_2 )) (PreH11 : (((list_to_Z (UINT_MOD) (l_rp_2)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))) (PreH12 : (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre ))) (PreH13 : (n_pre > 0)) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (0 <= vl_pre)) (PreH16 : (vl_pre <= UINT_MAX)) (PreH17 : (list_within_bound UINT_MOD l )),
  (((list_to_Z (UINT_MOD) ((app (l_rp_2) ((cons ((unsigned_last_nbits ((lpl + cl )) (32))) ((@nil Z))))))) + ((0 + hpl ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) * vl_pre ))
.

Definition mpn_mul_1_entail_wit_5_1_split_goal_2 :=
forall (l: (@list Z)) (n_pre: Z) (vl_pre: Z) (l_rp_2: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits ((lpl + cl )) (32)) >= cl)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= cl)) (PreH5 : (cl <= UINT_MAX)) (PreH6 : (0 <= lpl)) (PreH7 : (lpl <= UINT_MAX)) (PreH8 : (0 <= hpl)) (PreH9 : (hpl <= UINT_MAX)) (PreH10 : (list_within_bound UINT_MOD l_rp_2 )) (PreH11 : (((list_to_Z (UINT_MOD) (l_rp_2)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))) (PreH12 : (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre ))) (PreH13 : (n_pre > 0)) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (0 <= vl_pre)) (PreH16 : (vl_pre <= UINT_MAX)) (PreH17 : (list_within_bound UINT_MOD l )),
  (list_within_bound UINT_MOD (app (l_rp_2) ((cons ((unsigned_last_nbits ((lpl + cl )) (32))) ((@nil Z))))) )
.

Definition mpn_mul_1_entail_wit_5_2 :=
(
forall (l: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (vl_pre: Z) (l_rp_2: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits ((lpl + cl )) (32)) < cl)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= cl)) (PreH5 : (cl <= UINT_MAX)) (PreH6 : (0 <= lpl)) (PreH7 : (lpl <= UINT_MAX)) (PreH8 : (0 <= hpl)) (PreH9 : (hpl <= UINT_MAX)) (PreH10 : (list_within_bound UINT_MOD l_rp_2 )) (PreH11 : (((list_to_Z (UINT_MOD) (l_rp_2)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))) (PreH12 : (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre ))) (PreH13 : (n_pre > 0)) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (0 <= vl_pre)) (PreH16 : (vl_pre <= UINT_MAX)) (PreH17 : (list_within_bound UINT_MOD l )),
  (UIntArray.seg rp_pre 0 (i + 1 ) (app (l_rp_2) ((cons ((unsigned_last_nbits ((lpl + cl )) (32))) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  ((( &( "lpl" ) )) # UInt  |-> (unsigned_last_nbits ((lpl + cl )) (32)))
  **  ((( &( "hpl" ) )) # UInt  |-> hpl)
  **  ((( &( "ul" ) )) # UInt  |-> (Znth i l 0))
  **  (UIntArray.full up_pre n_pre l )
|--
  EX (l_rp: (@list Z)),
  “ (0 < n_pre) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (0 <= vl_pre) ”
  &&  “ (vl_pre <= UINT_MAX) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ (0 <= (unsigned_last_nbits ((1 + hpl )) (32))) ”
  &&  “ ((unsigned_last_nbits ((1 + hpl )) (32)) <= UINT_MAX) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ (list_within_bound UINT_MOD l_rp ) ”
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + ((unsigned_last_nbits ((1 + hpl )) (32)) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) * vl_pre )) ”
  &&  ((( &( "ul" ) )) # UInt  |->_)
  **  ((( &( "lpl" ) )) # UInt  |->_)
  **  ((( &( "hpl" ) )) # UInt  |->_)
  **  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 (i + 1 ) l_rp )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
) \/
(
forall (l: (@list Z)) (n_pre: Z) (vl_pre: Z) (l_rp_2: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits ((lpl + cl )) (32)) < cl)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= cl)) (PreH5 : (cl <= UINT_MAX)) (PreH6 : (0 <= lpl)) (PreH7 : (lpl <= UINT_MAX)) (PreH8 : (0 <= hpl)) (PreH9 : (hpl <= UINT_MAX)) (PreH10 : (list_within_bound UINT_MOD l_rp_2 )) (PreH11 : (((list_to_Z (UINT_MOD) (l_rp_2)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))) (PreH12 : (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre ))) (PreH13 : (n_pre > 0)) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (0 <= vl_pre)) (PreH16 : (vl_pre <= UINT_MAX)) (PreH17 : (list_within_bound UINT_MOD l )),
  TT && emp 
|--
  “ (((list_to_Z (UINT_MOD) ((app (l_rp_2) ((cons ((unsigned_last_nbits ((lpl + cl )) (32))) ((@nil Z))))))) + ((unsigned_last_nbits ((1 + hpl )) (32)) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) * vl_pre )) ”
  &&  “ (list_within_bound UINT_MOD (app (l_rp_2) ((cons ((unsigned_last_nbits ((lpl + cl )) (32))) ((@nil Z))))) ) ”
  &&  “ ((unsigned_last_nbits ((1 + hpl )) (32)) <= UINT_MAX) ”
  &&  “ (0 <= (unsigned_last_nbits ((1 + hpl )) (32))) ”
  &&  emp
).

Definition mpn_mul_1_entail_wit_5_2_split_goal_1 :=
forall (l: (@list Z)) (n_pre: Z) (vl_pre: Z) (l_rp_2: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits ((lpl + cl )) (32)) < cl)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= cl)) (PreH5 : (cl <= UINT_MAX)) (PreH6 : (0 <= lpl)) (PreH7 : (lpl <= UINT_MAX)) (PreH8 : (0 <= hpl)) (PreH9 : (hpl <= UINT_MAX)) (PreH10 : (list_within_bound UINT_MOD l_rp_2 )) (PreH11 : (((list_to_Z (UINT_MOD) (l_rp_2)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))) (PreH12 : (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre ))) (PreH13 : (n_pre > 0)) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (0 <= vl_pre)) (PreH16 : (vl_pre <= UINT_MAX)) (PreH17 : (list_within_bound UINT_MOD l )),
  (((list_to_Z (UINT_MOD) ((app (l_rp_2) ((cons ((unsigned_last_nbits ((lpl + cl )) (32))) ((@nil Z))))))) + ((unsigned_last_nbits ((1 + hpl )) (32)) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) * vl_pre ))
.

Definition mpn_mul_1_entail_wit_5_2_split_goal_2 :=
forall (l: (@list Z)) (n_pre: Z) (vl_pre: Z) (l_rp_2: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits ((lpl + cl )) (32)) < cl)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= cl)) (PreH5 : (cl <= UINT_MAX)) (PreH6 : (0 <= lpl)) (PreH7 : (lpl <= UINT_MAX)) (PreH8 : (0 <= hpl)) (PreH9 : (hpl <= UINT_MAX)) (PreH10 : (list_within_bound UINT_MOD l_rp_2 )) (PreH11 : (((list_to_Z (UINT_MOD) (l_rp_2)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))) (PreH12 : (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre ))) (PreH13 : (n_pre > 0)) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (0 <= vl_pre)) (PreH16 : (vl_pre <= UINT_MAX)) (PreH17 : (list_within_bound UINT_MOD l )),
  (list_within_bound UINT_MOD (app (l_rp_2) ((cons ((unsigned_last_nbits ((lpl + cl )) (32))) ((@nil Z))))) )
.

Definition mpn_mul_1_entail_wit_5_2_split_goal_3 :=
forall (l: (@list Z)) (n_pre: Z) (vl_pre: Z) (l_rp_2: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits ((lpl + cl )) (32)) < cl)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= cl)) (PreH5 : (cl <= UINT_MAX)) (PreH6 : (0 <= lpl)) (PreH7 : (lpl <= UINT_MAX)) (PreH8 : (0 <= hpl)) (PreH9 : (hpl <= UINT_MAX)) (PreH10 : (list_within_bound UINT_MOD l_rp_2 )) (PreH11 : (((list_to_Z (UINT_MOD) (l_rp_2)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))) (PreH12 : (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre ))) (PreH13 : (n_pre > 0)) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (0 <= vl_pre)) (PreH16 : (vl_pre <= UINT_MAX)) (PreH17 : (list_within_bound UINT_MOD l )),
  ((unsigned_last_nbits ((1 + hpl )) (32)) <= UINT_MAX)
.

Definition mpn_mul_1_entail_wit_5_2_split_goal_4 :=
forall (l: (@list Z)) (n_pre: Z) (vl_pre: Z) (l_rp_2: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits ((lpl + cl )) (32)) < cl)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= cl)) (PreH5 : (cl <= UINT_MAX)) (PreH6 : (0 <= lpl)) (PreH7 : (lpl <= UINT_MAX)) (PreH8 : (0 <= hpl)) (PreH9 : (hpl <= UINT_MAX)) (PreH10 : (list_within_bound UINT_MOD l_rp_2 )) (PreH11 : (((list_to_Z (UINT_MOD) (l_rp_2)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))) (PreH12 : (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre ))) (PreH13 : (n_pre > 0)) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (0 <= vl_pre)) (PreH16 : (vl_pre <= UINT_MAX)) (PreH17 : (list_within_bound UINT_MOD l )),
  (0 <= (unsigned_last_nbits ((1 + hpl )) (32)))
.

Definition mpn_mul_1_return_wit_1 :=
(
forall (l: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (vl_pre: Z) (l_rp: (@list Z)) (cl: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (0 <= vl_pre)) (PreH5 : (vl_pre <= UINT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cl)) (PreH9 : (cl <= UINT_MAX)) (PreH10 : (list_within_bound UINT_MOD l )) (PreH11 : (list_within_bound UINT_MOD l_rp )) (PreH12 : (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))),
  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i l_rp )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  EX (val': Z) (l': (@list Z)),
  “ ((Zlength (l')) = n_pre) ”
  &&  “ (list_within_bound UINT_MOD l' ) ”
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val') ”
  &&  “ ((val' + (cl * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l)) * vl_pre )) ”
  &&  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.full rp_pre n_pre l' )
) \/
(
forall (l: (@list Z)) (n_pre: Z) (vl_pre: Z) (l_rp: (@list Z)) (cl: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (0 <= vl_pre)) (PreH5 : (vl_pre <= UINT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cl)) (PreH9 : (cl <= UINT_MAX)) (PreH10 : (list_within_bound UINT_MOD l )) (PreH11 : (list_within_bound UINT_MOD l_rp )) (PreH12 : (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))),
  TT && emp 
|--
  “ (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l)) * vl_pre )) ”
  &&  “ ((Zlength (l_rp)) = n_pre) ”
  &&  emp
).

Definition mpn_mul_1_return_wit_1_split_goal_1 :=
forall (l: (@list Z)) (n_pre: Z) (vl_pre: Z) (l_rp: (@list Z)) (cl: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (0 <= vl_pre)) (PreH5 : (vl_pre <= UINT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cl)) (PreH9 : (cl <= UINT_MAX)) (PreH10 : (list_within_bound UINT_MOD l )) (PreH11 : (list_within_bound UINT_MOD l_rp )) (PreH12 : (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))),
  (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l)) * vl_pre ))
.

Definition mpn_mul_1_return_wit_1_split_goal_2 :=
forall (l: (@list Z)) (n_pre: Z) (vl_pre: Z) (l_rp: (@list Z)) (cl: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (0 <= vl_pre)) (PreH5 : (vl_pre <= UINT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cl)) (PreH9 : (cl <= UINT_MAX)) (PreH10 : (list_within_bound UINT_MOD l )) (PreH11 : (list_within_bound UINT_MOD l_rp )) (PreH12 : (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))),
  ((Zlength (l_rp)) = n_pre)
.

Definition mpn_mul_1_partial_solve_wit_1 :=
forall (l: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (vl_pre: Z) (l_rp: (@list Z)) (cl: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (0 <= vl_pre)) (PreH5 : (vl_pre <= UINT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cl)) (PreH9 : (cl <= UINT_MAX)) (PreH10 : (list_within_bound UINT_MOD l )) (PreH11 : (list_within_bound UINT_MOD l_rp )) (PreH12 : (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))),
  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i l_rp )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ (i < n_pre) ”
  &&  “ (0 < n_pre) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (0 <= vl_pre) ”
  &&  “ (vl_pre <= UINT_MAX) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= cl) ”
  &&  “ (cl <= UINT_MAX) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ (list_within_bound UINT_MOD l_rp ) ”
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre )) ”
  &&  (((up_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth i l 0))
  **  (UIntArray.missing_i up_pre i 0 n_pre l )
  **  (UIntArray.seg rp_pre 0 i l_rp )
  **  (UIntArray.undef_seg rp_pre i n_pre )
.

Definition mpn_mul_1_partial_solve_wit_2 :=
forall (l: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (vl_pre: Z) (l_rp: (@list Z)) (cl: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (0 <= vl_pre)) (PreH5 : (vl_pre <= UINT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cl)) (PreH9 : (cl <= UINT_MAX)) (PreH10 : (list_within_bound UINT_MOD l )) (PreH11 : (list_within_bound UINT_MOD l_rp )) (PreH12 : (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))),
  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i l_rp )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ (i < n_pre) ”
  &&  “ (0 < n_pre) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (0 <= vl_pre) ”
  &&  “ (vl_pre <= UINT_MAX) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ (0 <= cl) ”
  &&  “ (cl <= UINT_MAX) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  “ (list_within_bound UINT_MOD l_rp ) ”
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre )) ”
  &&  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i l_rp )
  **  (UIntArray.undef_seg rp_pre i n_pre )
.

Definition mpn_mul_1_partial_solve_wit_3 :=
forall (l: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (vl_pre: Z) (l_rp: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits ((lpl + cl )) (32)) >= cl)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= cl)) (PreH5 : (cl <= UINT_MAX)) (PreH6 : (0 <= lpl)) (PreH7 : (lpl <= UINT_MAX)) (PreH8 : (0 <= hpl)) (PreH9 : (hpl <= UINT_MAX)) (PreH10 : (list_within_bound UINT_MOD l_rp )) (PreH11 : (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))) (PreH12 : (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre ))) (PreH13 : (n_pre > 0)) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (0 <= vl_pre)) (PreH16 : (vl_pre <= UINT_MAX)) (PreH17 : (list_within_bound UINT_MOD l )),
  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i l_rp )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ ((unsigned_last_nbits ((lpl + cl )) (32)) >= cl) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= cl) ”
  &&  “ (cl <= UINT_MAX) ”
  &&  “ (0 <= lpl) ”
  &&  “ (lpl <= UINT_MAX) ”
  &&  “ (0 <= hpl) ”
  &&  “ (hpl <= UINT_MAX) ”
  &&  “ (list_within_bound UINT_MOD l_rp ) ”
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre )) ”
  &&  “ (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre )) ”
  &&  “ (n_pre > 0) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (0 <= vl_pre) ”
  &&  “ (vl_pre <= UINT_MAX) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i l_rp )
.

Definition mpn_mul_1_partial_solve_wit_4 :=
forall (l: (@list Z)) (rp_pre: Z) (up_pre: Z) (n_pre: Z) (vl_pre: Z) (l_rp: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits ((lpl + cl )) (32)) < cl)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= cl)) (PreH5 : (cl <= UINT_MAX)) (PreH6 : (0 <= lpl)) (PreH7 : (lpl <= UINT_MAX)) (PreH8 : (0 <= hpl)) (PreH9 : (hpl <= UINT_MAX)) (PreH10 : (list_within_bound UINT_MOD l_rp )) (PreH11 : (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))) (PreH12 : (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre ))) (PreH13 : (n_pre > 0)) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (0 <= vl_pre)) (PreH16 : (vl_pre <= UINT_MAX)) (PreH17 : (list_within_bound UINT_MOD l )),
  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i l_rp )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ ((unsigned_last_nbits ((lpl + cl )) (32)) < cl) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (0 <= cl) ”
  &&  “ (cl <= UINT_MAX) ”
  &&  “ (0 <= lpl) ”
  &&  “ (lpl <= UINT_MAX) ”
  &&  “ (0 <= hpl) ”
  &&  “ (hpl <= UINT_MAX) ”
  &&  “ (list_within_bound UINT_MOD l_rp ) ”
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre )) ”
  &&  “ (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre )) ”
  &&  “ (n_pre > 0) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (0 <= vl_pre) ”
  &&  “ (vl_pre <= UINT_MAX) ”
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i l_rp )
.

(*----- Function mpz_clear -----*)

Definition mpz_clear_return_wit_1 :=
forall (n: Z) (r_pre: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign n size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (cap_2 <> 0)),
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
|--
  EX (ptr: Z) (cap: Z) (size: Z),
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_clear_return_wit_2 :=
(
forall (n: Z) (r_pre: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign n size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (cap_2 = 0)),
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (n)) (Zabs (size_2)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
|--
  EX (ptr: Z) (cap: Z) (size: Z),
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
) \/
(
forall (n: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign n size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (cap_2 = 0)),
  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (n)) (Zabs (size_2)) )
|--
  TT && emp 
).

Definition mpz_clear_return_wit_2_split_goal_spatial :=
forall (n: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign n size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (cap_2 = 0)),
  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (n)) (Zabs (size_2)) )
|--
  TT && emp 
.

Definition mpz_clear_partial_solve_wit_1 :=
forall (n: Z) (r_pre: Z),
  (store_Z r_pre n )
|--
  EX (ptr: Z) (size: Z) (cap: Z),
  “ (same_sign n size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
.

Definition mpz_clear_partial_solve_wit_2 :=
forall (n: Z) (r_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign n size )) (PreH2 : ((Zabs (size)) <= cap)) (PreH3 : (cap <> 0)),
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
|--
  “ (same_sign n size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (cap <> 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
.

(*----- Function mpz_sgn -----*)

Definition mpz_sgn_safety_wit_1 :=
forall (n: Z) (u_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign n size )) (PreH2 : ((Zabs (size)) <= cap)),
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_sgn_return_wit_1 :=
(
forall (n: Z) (u_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (size < 0)) (PreH2 : (retval = (-1))) (PreH3 : (same_sign n size )) (PreH4 : ((Zabs (size)) <= cap)),
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
|--
  “ (n < 0) ”
  &&  “ (retval = (-1)) ”
  &&  (store_Z u_pre n )
) \/
(
forall (n: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (size < 0)) (PreH2 : (retval = (-1))) (PreH3 : (same_sign n size )) (PreH4 : ((Zabs (size)) <= cap)),
  TT && emp 
|--
  “ (n < 0) ”
  &&  emp
).

Definition mpz_sgn_return_wit_1_split_goal_1 :=
forall (n: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (size < 0)) (PreH2 : (retval = (-1))) (PreH3 : (same_sign n size )) (PreH4 : ((Zabs (size)) <= cap)),
  (n < 0)
.

Definition mpz_sgn_return_wit_2 :=
(
forall (n: Z) (u_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (size = 0)) (PreH2 : (retval = 0)) (PreH3 : (same_sign n size )) (PreH4 : ((Zabs (size)) <= cap)),
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
|--
  “ (n = 0) ”
  &&  “ (retval = 0) ”
  &&  (store_Z u_pre n )
) \/
(
forall (n: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (size = 0)) (PreH2 : (retval = 0)) (PreH3 : (same_sign n size )) (PreH4 : ((Zabs (size)) <= cap)),
  TT && emp 
|--
  “ (n = 0) ”
  &&  emp
).

Definition mpz_sgn_return_wit_2_split_goal_1 :=
forall (n: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (size = 0)) (PreH2 : (retval = 0)) (PreH3 : (same_sign n size )) (PreH4 : ((Zabs (size)) <= cap)),
  (n = 0)
.

Definition mpz_sgn_return_wit_3 :=
(
forall (n: Z) (u_pre: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (size > 0)) (PreH2 : (retval = 1)) (PreH3 : (same_sign n size )) (PreH4 : ((Zabs (size)) <= cap)),
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
|--
  “ (n > 0) ”
  &&  “ (retval = 1) ”
  &&  (store_Z u_pre n )
) \/
(
forall (n: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (size > 0)) (PreH2 : (retval = 1)) (PreH3 : (same_sign n size )) (PreH4 : ((Zabs (size)) <= cap)),
  TT && emp 
|--
  “ (n > 0) ”
  &&  emp
).

Definition mpz_sgn_return_wit_3_split_goal_1 :=
forall (n: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (size > 0)) (PreH2 : (retval = 1)) (PreH3 : (same_sign n size )) (PreH4 : ((Zabs (size)) <= cap)),
  (n > 0)
.

Definition mpz_sgn_partial_solve_wit_1 :=
forall (n: Z) (u_pre: Z),
  (store_Z u_pre n )
|--
  EX (ptr: Z) (size: Z) (cap: Z),
  “ (same_sign n size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
.

Definition mpz_sgn_partial_solve_wit_2 :=
forall (n: Z) (u_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign n size )) (PreH2 : ((Zabs (size)) <= cap)),
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
|--
  “ (same_sign n size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_gmp_abs_safety_wit_1 : gmp_abs_safety_wit_1.
Axiom proof_of_gmp_abs_safety_wit_2 : gmp_abs_safety_wit_2.
Axiom proof_of_gmp_abs_return_wit_1 : gmp_abs_return_wit_1.
Axiom proof_of_gmp_abs_return_wit_2 : gmp_abs_return_wit_2.
Axiom proof_of_gmp_max_return_wit_1 : gmp_max_return_wit_1.
Axiom proof_of_gmp_max_return_wit_2 : gmp_max_return_wit_2.
Axiom proof_of_gmp_cmp_safety_wit_1 : gmp_cmp_safety_wit_1.
Axiom proof_of_gmp_cmp_safety_wit_2 : gmp_cmp_safety_wit_2.
Axiom proof_of_gmp_cmp_safety_wit_3 : gmp_cmp_safety_wit_3.
Axiom proof_of_gmp_cmp_safety_wit_4 : gmp_cmp_safety_wit_4.
Axiom proof_of_gmp_cmp_return_wit_1 : gmp_cmp_return_wit_1.
Axiom proof_of_gmp_cmp_return_wit_2 : gmp_cmp_return_wit_2.
Axiom proof_of_gmp_cmp_return_wit_3 : gmp_cmp_return_wit_3.
Axiom proof_of_mpn_cmp_safety_wit_1 : mpn_cmp_safety_wit_1.
Axiom proof_of_mpn_cmp_safety_wit_2 : mpn_cmp_safety_wit_2.
Axiom proof_of_mpn_cmp_safety_wit_3 : mpn_cmp_safety_wit_3.
Axiom proof_of_mpn_cmp_safety_wit_4 : mpn_cmp_safety_wit_4.
Axiom proof_of_mpn_cmp_safety_wit_5 : mpn_cmp_safety_wit_5.
Axiom proof_of_mpn_cmp_safety_wit_6 : mpn_cmp_safety_wit_6.
Axiom proof_of_mpn_cmp_safety_wit_7 : mpn_cmp_safety_wit_7.
Axiom proof_of_mpn_cmp_entail_wit_1 : mpn_cmp_entail_wit_1.
Axiom proof_of_mpn_cmp_entail_wit_2 : mpn_cmp_entail_wit_2.
Axiom proof_of_mpn_cmp_return_wit_1 : mpn_cmp_return_wit_1.
Axiom proof_of_mpn_cmp_return_wit_2 : mpn_cmp_return_wit_2.
Axiom proof_of_mpn_cmp_return_wit_3 : mpn_cmp_return_wit_3.
Axiom proof_of_mpn_cmp_partial_solve_wit_1 : mpn_cmp_partial_solve_wit_1.
Axiom proof_of_mpn_cmp_partial_solve_wit_2 : mpn_cmp_partial_solve_wit_2.
Axiom proof_of_mpn_cmp_partial_solve_wit_3 : mpn_cmp_partial_solve_wit_3.
Axiom proof_of_mpn_cmp_partial_solve_wit_4 : mpn_cmp_partial_solve_wit_4.
Axiom proof_of_mpn_cmp_partial_solve_wit_5 : mpn_cmp_partial_solve_wit_5.
Axiom proof_of_mpn_cmp_which_implies_wit_1 : mpn_cmp_which_implies_wit_1.
Axiom proof_of_mpn_cmp4_safety_wit_1 : mpn_cmp4_safety_wit_1.
Axiom proof_of_mpn_cmp4_safety_wit_2 : mpn_cmp4_safety_wit_2.
Axiom proof_of_mpn_cmp4_safety_wit_3 : mpn_cmp4_safety_wit_3.
Axiom proof_of_mpn_cmp4_return_wit_1 : mpn_cmp4_return_wit_1.
Axiom proof_of_mpn_cmp4_return_wit_2 : mpn_cmp4_return_wit_2.
Axiom proof_of_mpn_cmp4_return_wit_3 : mpn_cmp4_return_wit_3.
Axiom proof_of_mpn_cmp4_return_wit_4 : mpn_cmp4_return_wit_4.
Axiom proof_of_mpn_cmp4_return_wit_5 : mpn_cmp4_return_wit_5.
Axiom proof_of_mpn_cmp4_partial_solve_wit_1_pure : mpn_cmp4_partial_solve_wit_1_pure.
Axiom proof_of_mpn_cmp4_partial_solve_wit_1 : mpn_cmp4_partial_solve_wit_1.
Axiom proof_of_gmp_umul_ppmm_safety_wit_1 : gmp_umul_ppmm_safety_wit_1.
Axiom proof_of_gmp_umul_ppmm_safety_wit_2 : gmp_umul_ppmm_safety_wit_2.
Axiom proof_of_gmp_umul_ppmm_safety_wit_3 : gmp_umul_ppmm_safety_wit_3.
Axiom proof_of_gmp_umul_ppmm_safety_wit_4 : gmp_umul_ppmm_safety_wit_4.
Axiom proof_of_gmp_umul_ppmm_safety_wit_5 : gmp_umul_ppmm_safety_wit_5.
Axiom proof_of_gmp_umul_ppmm_safety_wit_6 : gmp_umul_ppmm_safety_wit_6.
Axiom proof_of_gmp_umul_ppmm_safety_wit_7 : gmp_umul_ppmm_safety_wit_7.
Axiom proof_of_gmp_umul_ppmm_safety_wit_8 : gmp_umul_ppmm_safety_wit_8.
Axiom proof_of_gmp_umul_ppmm_safety_wit_9 : gmp_umul_ppmm_safety_wit_9.
Axiom proof_of_gmp_umul_ppmm_safety_wit_10 : gmp_umul_ppmm_safety_wit_10.
Axiom proof_of_gmp_umul_ppmm_safety_wit_11 : gmp_umul_ppmm_safety_wit_11.
Axiom proof_of_gmp_umul_ppmm_safety_wit_12 : gmp_umul_ppmm_safety_wit_12.
Axiom proof_of_gmp_umul_ppmm_safety_wit_13 : gmp_umul_ppmm_safety_wit_13.
Axiom proof_of_gmp_umul_ppmm_safety_wit_14 : gmp_umul_ppmm_safety_wit_14.
Axiom proof_of_gmp_umul_ppmm_safety_wit_15 : gmp_umul_ppmm_safety_wit_15.
Axiom proof_of_gmp_umul_ppmm_safety_wit_16 : gmp_umul_ppmm_safety_wit_16.
Axiom proof_of_gmp_umul_ppmm_safety_wit_17 : gmp_umul_ppmm_safety_wit_17.
Axiom proof_of_gmp_umul_ppmm_safety_wit_18 : gmp_umul_ppmm_safety_wit_18.
Axiom proof_of_gmp_umul_ppmm_safety_wit_19 : gmp_umul_ppmm_safety_wit_19.
Axiom proof_of_gmp_umul_ppmm_entail_wit_1 : gmp_umul_ppmm_entail_wit_1.
Axiom proof_of_gmp_umul_ppmm_entail_wit_2 : gmp_umul_ppmm_entail_wit_2.
Axiom proof_of_gmp_umul_ppmm_return_wit_1 : gmp_umul_ppmm_return_wit_1.
Axiom proof_of_gmp_umul_ppmm_return_wit_2 : gmp_umul_ppmm_return_wit_2.
Axiom proof_of_mpn_mul_1_safety_wit_1 : mpn_mul_1_safety_wit_1.
Axiom proof_of_mpn_mul_1_safety_wit_2 : mpn_mul_1_safety_wit_2.
Axiom proof_of_mpn_mul_1_safety_wit_3 : mpn_mul_1_safety_wit_3.
Axiom proof_of_mpn_mul_1_safety_wit_4 : mpn_mul_1_safety_wit_4.
Axiom proof_of_mpn_mul_1_safety_wit_5 : mpn_mul_1_safety_wit_5.
Axiom proof_of_mpn_mul_1_safety_wit_6 : mpn_mul_1_safety_wit_6.
Axiom proof_of_mpn_mul_1_entail_wit_1 : mpn_mul_1_entail_wit_1.
Axiom proof_of_mpn_mul_1_entail_wit_2 : mpn_mul_1_entail_wit_2.
Axiom proof_of_mpn_mul_1_entail_wit_3 : mpn_mul_1_entail_wit_3.
Axiom proof_of_mpn_mul_1_entail_wit_4 : mpn_mul_1_entail_wit_4.
Axiom proof_of_mpn_mul_1_entail_wit_5_1 : mpn_mul_1_entail_wit_5_1.
Axiom proof_of_mpn_mul_1_entail_wit_5_2 : mpn_mul_1_entail_wit_5_2.
Axiom proof_of_mpn_mul_1_return_wit_1 : mpn_mul_1_return_wit_1.
Axiom proof_of_mpn_mul_1_partial_solve_wit_1 : mpn_mul_1_partial_solve_wit_1.
Axiom proof_of_mpn_mul_1_partial_solve_wit_2 : mpn_mul_1_partial_solve_wit_2.
Axiom proof_of_mpn_mul_1_partial_solve_wit_3 : mpn_mul_1_partial_solve_wit_3.
Axiom proof_of_mpn_mul_1_partial_solve_wit_4 : mpn_mul_1_partial_solve_wit_4.
Axiom proof_of_mpz_clear_return_wit_1 : mpz_clear_return_wit_1.
Axiom proof_of_mpz_clear_return_wit_2 : mpz_clear_return_wit_2.
Axiom proof_of_mpz_clear_partial_solve_wit_1 : mpz_clear_partial_solve_wit_1.
Axiom proof_of_mpz_clear_partial_solve_wit_2 : mpz_clear_partial_solve_wit_2.
Axiom proof_of_mpz_sgn_safety_wit_1 : mpz_sgn_safety_wit_1.
Axiom proof_of_mpz_sgn_return_wit_1 : mpz_sgn_return_wit_1.
Axiom proof_of_mpz_sgn_return_wit_2 : mpz_sgn_return_wit_2.
Axiom proof_of_mpz_sgn_return_wit_3 : mpz_sgn_return_wit_3.
Axiom proof_of_mpz_sgn_partial_solve_wit_1 : mpz_sgn_partial_solve_wit_1.
Axiom proof_of_mpz_sgn_partial_solve_wit_2 : mpz_sgn_partial_solve_wit_2.

End VC_Correct.
