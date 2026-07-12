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
Require Import SimpleC.EE.Applications_human.minigmp.GmpAux SimpleC.EE.Applications_human.minigmp.GmpNumber.
Import Aux.
Local Open Scope sac.
Require Import gmp_strategy_goal.
Require Import gmp_strategy_proof.

(*----- Function gmp_abs -----*)

Definition gmp_abs_safety_wit_1 := 
forall (x_pre: Z) (PreH1 : (INT_MIN < x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition gmp_abs_safety_wit_2 := 
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (x_pre <> (INT_MIN)) ”
.

Definition gmp_abs_return_wit_1 := 
(
forall (x_pre: Z) (PreH1 : (x_pre >= 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (x_pre = (Zabs (x_pre))) ”
  &&  emp
) \/
(
forall (x_pre: Z) (PreH1 : (x_pre >= 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (x_pre = (Zabs (x_pre))) ”
  &&  emp
).

Definition gmp_abs_return_wit_1_split_goal_1 := 
forall (x_pre: Z) (PreH1 : (x_pre >= 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  (x_pre = (Zabs (x_pre)))
.

Definition gmp_abs_return_wit_2 := 
(
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((-x_pre) = (Zabs (x_pre))) ”
  &&  emp
) \/
(
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((-x_pre) = (Zabs (x_pre))) ”
  &&  emp
).

Definition gmp_abs_return_wit_2_split_goal_1 := 
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  ((-x_pre) = (Zabs (x_pre)))
.

(*----- Function gmp_max -----*)

Definition gmp_max_return_wit_1 := 
(
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre > b_pre)) ,
  TT && emp 
|--
  “ (a_pre = (Z.max (a_pre) (b_pre))) ”
  &&  emp
) \/
(
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre > b_pre)) ,
  TT && emp 
|--
  “ (a_pre = (Z.max (a_pre) (b_pre))) ”
  &&  emp
).

Definition gmp_max_return_wit_1_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre > b_pre)) ,
  (a_pre = (Z.max (a_pre) (b_pre)))
.

Definition gmp_max_return_wit_2 := 
(
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <= b_pre)) ,
  TT && emp 
|--
  “ (b_pre = (Z.max (a_pre) (b_pre))) ”
  &&  emp
) \/
(
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <= b_pre)) ,
  TT && emp 
|--
  “ (b_pre = (Z.max (a_pre) (b_pre))) ”
  &&  emp
).

Definition gmp_max_return_wit_2_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <= b_pre)) ,
  (b_pre = (Z.max (a_pre) (b_pre)))
.

(*----- Function gmp_cmp -----*)

Definition gmp_cmp_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre >= b_pre)) (PreH2 : (a_pre > b_pre)) ,
  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((1 - 0 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (1 - 0 )) ”
.

Definition gmp_cmp_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre < b_pre)) (PreH2 : (a_pre <= b_pre)) ,
  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((0 - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (0 - 1 )) ”
.

Definition gmp_cmp_safety_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre >= b_pre)) (PreH2 : (a_pre <= b_pre)) ,
  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((0 - 0 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (0 - 0 )) ”
.

Definition gmp_cmp_safety_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre < b_pre)) (PreH2 : (a_pre > b_pre)) ,
  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ False ”
.

Definition gmp_cmp_return_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre >= b_pre)) (PreH2 : (a_pre <= b_pre)) ,
  TT && emp 
|--
  “ (a_pre = b_pre) ” 
  &&  “ ((0 - 0 ) = 0) ”
  &&  emp
.

Definition gmp_cmp_return_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre < b_pre)) (PreH2 : (a_pre <= b_pre)) ,
  TT && emp 
|--
  “ (a_pre < b_pre) ” 
  &&  “ ((0 - 1 ) = (-1)) ”
  &&  emp
.

Definition gmp_cmp_return_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre >= b_pre)) (PreH2 : (a_pre > b_pre)) ,
  TT && emp 
|--
  “ (a_pre > b_pre) ” 
  &&  “ ((1 - 0 ) = 1) ”
  &&  emp
.

(*----- Function mpn_copyi -----*)

Definition mpn_copyi_safety_wit_1 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (val: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH3 : (list_within_bound UINT_MOD l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (UIntArray.full s_pre n_pre l )
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  (UIntArray.undef_full d_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_copyi_safety_wit_2 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (val: Z) (l: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH6 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.full d_pre (i + 1 ) (app ((sublist (0) (i) (l))) ((cons ((Znth i l 0)) ((@nil Z))))) )
  **  (UIntArray.undef_seg d_pre (i + 1 ) n_pre )
  **  (UIntArray.full s_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_copyi_entail_wit_1 := 
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (val: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH3 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.full s_pre n_pre l )
  **  (UIntArray.undef_full d_pre n_pre )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full d_pre 0 (sublist (0) (0) (l)) )
  **  (UIntArray.undef_seg d_pre 0 n_pre )
  **  (UIntArray.full s_pre n_pre l )
) \/
(
forall (n_pre: Z) (val: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH3 : (list_within_bound UINT_MOD l )) ,
  TT && emp 
|--
  “ (0 <= n_pre) ” 
  &&  “ ((sublist (0) (0) (l)) = (@nil Z)) ”
  &&  emp
).

Definition mpn_copyi_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (val: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH3 : (list_within_bound UINT_MOD l )) ,
  (0 <= n_pre)
.

Definition mpn_copyi_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (val: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH3 : (list_within_bound UINT_MOD l )) ,
  ((sublist (0) (0) (l)) = (@nil Z))
.

Definition mpn_copyi_entail_wit_2 := 
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (val: Z) (l: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH6 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.full d_pre (i + 1 ) (app ((sublist (0) (i) (l))) ((cons ((Znth i l 0)) ((@nil Z))))) )
  **  (UIntArray.undef_seg d_pre (i + 1 ) n_pre )
  **  (UIntArray.full s_pre n_pre l )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full d_pre (i + 1 ) (sublist (0) ((i + 1 )) (l)) )
  **  (UIntArray.undef_seg d_pre (i + 1 ) n_pre )
  **  (UIntArray.full s_pre n_pre l )
) \/
(
forall (n_pre: Z) (val: Z) (l: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH6 : (list_within_bound UINT_MOD l )) ,
  TT && emp 
|--
  “ ((app ((sublist (0) (i) (l))) ((cons ((Znth i l 0)) ((@nil Z))))) = (sublist (0) ((i + 1 )) (l))) ”
  &&  emp
).

Definition mpn_copyi_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (val: Z) (l: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH6 : (list_within_bound UINT_MOD l )) ,
  ((app ((sublist (0) (i) (l))) ((cons ((Znth i l 0)) ((@nil Z))))) = (sublist (0) ((i + 1 )) (l)))
.

Definition mpn_copyi_return_wit_1 := 
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (val: Z) (l: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH6 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.full d_pre i (sublist (0) (i) (l)) )
  **  (UIntArray.undef_seg d_pre i n_pre )
  **  (UIntArray.full s_pre n_pre l )
|--
  (mpd_store_Z UINT_MOD s_pre val n_pre )
  **  (mpd_store_Z UINT_MOD d_pre val n_pre )
) \/
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (val: Z) (l: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH6 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.full d_pre i (sublist (0) (i) (l)) )
  **  (UIntArray.full s_pre n_pre l )
|--
  (mpd_store_Z UINT_MOD s_pre val n_pre )
  **  (mpd_store_Z UINT_MOD d_pre val n_pre )
).

Definition mpn_copyi_return_wit_1_split_goal_spatial := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (val: Z) (l: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH6 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.full d_pre i (sublist (0) (i) (l)) )
  **  (UIntArray.full s_pre n_pre l )
|--
  (mpd_store_Z UINT_MOD s_pre val n_pre )
  **  (mpd_store_Z UINT_MOD d_pre val n_pre )
.

Definition mpn_copyi_partial_solve_wit_1 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (val: Z) ,
  (mpd_store_Z UINT_MOD s_pre val n_pre )
  **  (UIntArray.undef_full d_pre n_pre )
|--
  (mpd_store_Z UINT_MOD s_pre val n_pre )
  **  (UIntArray.undef_full d_pre n_pre )
.

Definition mpn_copyi_partial_solve_wit_2 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (val: Z) (l: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH6 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.full d_pre i (sublist (0) (i) (l)) )
  **  (UIntArray.undef_seg d_pre i n_pre )
  **  (UIntArray.full s_pre n_pre l )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (((s_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth i l 0))
  **  (UIntArray.missing_i s_pre i 0 n_pre l )
  **  (UIntArray.full d_pre i (sublist (0) (i) (l)) )
  **  (UIntArray.undef_seg d_pre i n_pre )
.

Definition mpn_copyi_partial_solve_wit_3 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (val: Z) (l: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH6 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.full s_pre n_pre l )
  **  (UIntArray.full d_pre i (sublist (0) (i) (l)) )
  **  (UIntArray.undef_seg d_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (((d_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg d_pre (i + 1 ) n_pre )
  **  (UIntArray.full s_pre n_pre l )
  **  (UIntArray.full d_pre i (sublist (0) (i) (l)) )
.

Definition mpn_copyi_which_implies_wit_1 := 
(
forall (val: Z) (n: Z) (s: Z) ,
  (mpd_store_Z UINT_MOD s val n )
|--
  EX (l: (@list Z)) ,
  “ ((Zlength (l)) = n) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full s n l )
) \/
(
forall (val: Z) (n: Z) (s: Z) ,
  (mpd_store_Z UINT_MOD s val n )
|--
  EX (l: (@list Z)) ,
  “ ((Zlength (l)) = n) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full s n l )
).

(*----- Function mpn_cmp -----*)

Definition mpn_cmp_safety_wit_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH2 : ((last (l1) (1)) >= 1)) (PreH3 : (list_within_bound UINT_MOD l1 )) (PreH4 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH5 : ((last (l2) (1)) >= 1)) (PreH6 : (list_within_bound UINT_MOD l2 )) (PreH7 : (n_pre = (Zlength (l1)))) (PreH8 : (n_pre = (Zlength (l2)))) (PreH9 : (0 <= n_pre)) ,
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
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((-1) <= n)) (PreH2 : (n < n_pre)) (PreH3 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH4 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH5 : ((last (l1) (1)) >= 1)) (PreH6 : (list_within_bound UINT_MOD l1 )) (PreH7 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH8 : ((last (l2) (1)) >= 1)) (PreH9 : (list_within_bound UINT_MOD l2 )) (PreH10 : (n_pre = (Zlength (l1)))) (PreH11 : (n_pre = (Zlength (l2)))) (PreH12 : (0 <= n_pre)) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.full ap_pre n_pre l1 )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.full bp_pre n_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_cmp_safety_wit_3 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((Znth n l1 0) > (Znth n l2 0))) (PreH2 : ((Znth n l1 0) <> (Znth n l2 0))) (PreH3 : (n >= 0)) (PreH4 : ((-1) <= n)) (PreH5 : (n < n_pre)) (PreH6 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH7 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH8 : ((last (l1) (1)) >= 1)) (PreH9 : (list_within_bound UINT_MOD l1 )) (PreH10 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH11 : ((last (l2) (1)) >= 1)) (PreH12 : (list_within_bound UINT_MOD l2 )) (PreH13 : (n_pre = (Zlength (l1)))) (PreH14 : (n_pre = (Zlength (l2)))) (PreH15 : (0 <= n_pre)) ,
  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_cmp_safety_wit_4 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((Znth n l1 0) <= (Znth n l2 0))) (PreH2 : ((Znth n l1 0) <> (Znth n l2 0))) (PreH3 : (n >= 0)) (PreH4 : ((-1) <= n)) (PreH5 : (n < n_pre)) (PreH6 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH7 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH8 : ((last (l1) (1)) >= 1)) (PreH9 : (list_within_bound UINT_MOD l1 )) (PreH10 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH11 : ((last (l2) (1)) >= 1)) (PreH12 : (list_within_bound UINT_MOD l2 )) (PreH13 : (n_pre = (Zlength (l1)))) (PreH14 : (n_pre = (Zlength (l2)))) (PreH15 : (0 <= n_pre)) ,
  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition mpn_cmp_safety_wit_5 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((Znth n l1 0) <= (Znth n l2 0))) (PreH2 : ((Znth n l1 0) <> (Znth n l2 0))) (PreH3 : (n >= 0)) (PreH4 : ((-1) <= n)) (PreH5 : (n < n_pre)) (PreH6 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH7 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH8 : ((last (l1) (1)) >= 1)) (PreH9 : (list_within_bound UINT_MOD l1 )) (PreH10 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH11 : ((last (l2) (1)) >= 1)) (PreH12 : (list_within_bound UINT_MOD l2 )) (PreH13 : (n_pre = (Zlength (l1)))) (PreH14 : (n_pre = (Zlength (l2)))) (PreH15 : (0 <= n_pre)) ,
  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_cmp_safety_wit_6 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((Znth n l1 0) = (Znth n l2 0))) (PreH2 : (n >= 0)) (PreH3 : ((-1) <= n)) (PreH4 : (n < n_pre)) (PreH5 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH6 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH7 : ((last (l1) (1)) >= 1)) (PreH8 : (list_within_bound UINT_MOD l1 )) (PreH9 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH10 : ((last (l2) (1)) >= 1)) (PreH11 : (list_within_bound UINT_MOD l2 )) (PreH12 : (n_pre = (Zlength (l1)))) (PreH13 : (n_pre = (Zlength (l2)))) (PreH14 : (0 <= n_pre)) ,
  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
|--
  “ ((n - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n - 1 )) ”
.

Definition mpn_cmp_safety_wit_7 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : (n < 0)) (PreH2 : ((-1) <= n)) (PreH3 : (n < n_pre)) (PreH4 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH5 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH6 : ((last (l1) (1)) >= 1)) (PreH7 : (list_within_bound UINT_MOD l1 )) (PreH8 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH9 : ((last (l2) (1)) >= 1)) (PreH10 : (list_within_bound UINT_MOD l2 )) (PreH11 : (n_pre = (Zlength (l1)))) (PreH12 : (n_pre = (Zlength (l2)))) (PreH13 : (0 <= n_pre)) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.full ap_pre n_pre l1 )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.full bp_pre n_pre l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_cmp_entail_wit_1 := 
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH2 : ((last (l1) (1)) >= 1)) (PreH3 : (list_within_bound UINT_MOD l1 )) (PreH4 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH5 : ((last (l2) (1)) >= 1)) (PreH6 : (list_within_bound UINT_MOD l2 )) (PreH7 : (n_pre = (Zlength (l1)))) (PreH8 : (n_pre = (Zlength (l2)))) (PreH9 : (0 <= n_pre)) ,
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
  &&  “ (n_pre = (Zlength (l1))) ” 
  &&  “ (n_pre = (Zlength (l2))) ” 
  &&  “ (0 <= n_pre) ”
  &&  (UIntArray.full ap_pre n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
) \/
(
forall (n_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH2 : ((last (l1) (1)) >= 1)) (PreH3 : (list_within_bound UINT_MOD l1 )) (PreH4 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH5 : ((last (l2) (1)) >= 1)) (PreH6 : (list_within_bound UINT_MOD l2 )) (PreH7 : (n_pre = (Zlength (l1)))) (PreH8 : (n_pre = (Zlength (l2)))) (PreH9 : (0 <= n_pre)) ,
  TT && emp 
|--
  “ ((sublist (((n_pre - 1 ) + 1 )) (n_pre) (l1)) = (sublist (((n_pre - 1 ) + 1 )) (n_pre) (l2))) ”
  &&  emp
).

Definition mpn_cmp_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH2 : ((last (l1) (1)) >= 1)) (PreH3 : (list_within_bound UINT_MOD l1 )) (PreH4 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH5 : ((last (l2) (1)) >= 1)) (PreH6 : (list_within_bound UINT_MOD l2 )) (PreH7 : (n_pre = (Zlength (l1)))) (PreH8 : (n_pre = (Zlength (l2)))) (PreH9 : (0 <= n_pre)) ,
  ((sublist (((n_pre - 1 ) + 1 )) (n_pre) (l1)) = (sublist (((n_pre - 1 ) + 1 )) (n_pre) (l2)))
.

Definition mpn_cmp_entail_wit_2 := 
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((Znth n l1 0) = (Znth n l2 0))) (PreH2 : (n >= 0)) (PreH3 : ((-1) <= n)) (PreH4 : (n < n_pre)) (PreH5 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH6 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH7 : ((last (l1) (1)) >= 1)) (PreH8 : (list_within_bound UINT_MOD l1 )) (PreH9 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH10 : ((last (l2) (1)) >= 1)) (PreH11 : (list_within_bound UINT_MOD l2 )) (PreH12 : (n_pre = (Zlength (l1)))) (PreH13 : (n_pre = (Zlength (l2)))) (PreH14 : (0 <= n_pre)) ,
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
  &&  “ (n_pre = (Zlength (l1))) ” 
  &&  “ (n_pre = (Zlength (l2))) ” 
  &&  “ (0 <= n_pre) ”
  &&  (UIntArray.full ap_pre n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
) \/
(
forall (n_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((Znth n l1 0) = (Znth n l2 0))) (PreH2 : (n >= 0)) (PreH3 : ((-1) <= n)) (PreH4 : (n < n_pre)) (PreH5 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH6 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH7 : ((last (l1) (1)) >= 1)) (PreH8 : (list_within_bound UINT_MOD l1 )) (PreH9 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH10 : ((last (l2) (1)) >= 1)) (PreH11 : (list_within_bound UINT_MOD l2 )) (PreH12 : (n_pre = (Zlength (l1)))) (PreH13 : (n_pre = (Zlength (l2)))) (PreH14 : (0 <= n_pre)) ,
  TT && emp 
|--
  “ ((sublist (((n - 1 ) + 1 )) (n_pre) (l1)) = (sublist (((n - 1 ) + 1 )) (n_pre) (l2))) ”
  &&  emp
).

Definition mpn_cmp_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((Znth n l1 0) = (Znth n l2 0))) (PreH2 : (n >= 0)) (PreH3 : ((-1) <= n)) (PreH4 : (n < n_pre)) (PreH5 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH6 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH7 : ((last (l1) (1)) >= 1)) (PreH8 : (list_within_bound UINT_MOD l1 )) (PreH9 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH10 : ((last (l2) (1)) >= 1)) (PreH11 : (list_within_bound UINT_MOD l2 )) (PreH12 : (n_pre = (Zlength (l1)))) (PreH13 : (n_pre = (Zlength (l2)))) (PreH14 : (0 <= n_pre)) ,
  ((sublist (((n - 1 ) + 1 )) (n_pre) (l1)) = (sublist (((n - 1 ) + 1 )) (n_pre) (l2)))
.

Definition mpn_cmp_return_wit_1 := 
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : (n < 0)) (PreH2 : ((-1) <= n)) (PreH3 : (n < n_pre)) (PreH4 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH5 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH6 : ((last (l1) (1)) >= 1)) (PreH7 : (list_within_bound UINT_MOD l1 )) (PreH8 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH9 : ((last (l2) (1)) >= 1)) (PreH10 : (list_within_bound UINT_MOD l2 )) (PreH11 : (n_pre = (Zlength (l1)))) (PreH12 : (n_pre = (Zlength (l2)))) (PreH13 : (0 <= n_pre)) ,
  (UIntArray.full ap_pre n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
|--
  “ (val1 = val2) ” 
  &&  “ (0 = 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre )
) \/
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : (n < 0)) (PreH2 : ((-1) <= n)) (PreH3 : (n < n_pre)) (PreH4 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH5 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH6 : ((last (l1) (1)) >= 1)) (PreH7 : (list_within_bound UINT_MOD l1 )) (PreH8 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH9 : ((last (l2) (1)) >= 1)) (PreH10 : (list_within_bound UINT_MOD l2 )) (PreH11 : (n_pre = (Zlength (l1)))) (PreH12 : (n_pre = (Zlength (l2)))) (PreH13 : (0 <= n_pre)) ,
  (UIntArray.full ap_pre n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
|--
  “ (val1 = val2) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre )
).

Definition mpn_cmp_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : (n < 0)) (PreH2 : ((-1) <= n)) (PreH3 : (n < n_pre)) (PreH4 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH5 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH6 : ((last (l1) (1)) >= 1)) (PreH7 : (list_within_bound UINT_MOD l1 )) (PreH8 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH9 : ((last (l2) (1)) >= 1)) (PreH10 : (list_within_bound UINT_MOD l2 )) (PreH11 : (n_pre = (Zlength (l1)))) (PreH12 : (n_pre = (Zlength (l2)))) (PreH13 : (0 <= n_pre)) ,
  (UIntArray.full ap_pre n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
|--
  “ (val1 = val2) ”
.

Definition mpn_cmp_return_wit_1_split_goal_spatial := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : (n < 0)) (PreH2 : ((-1) <= n)) (PreH3 : (n < n_pre)) (PreH4 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH5 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH6 : ((last (l1) (1)) >= 1)) (PreH7 : (list_within_bound UINT_MOD l1 )) (PreH8 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH9 : ((last (l2) (1)) >= 1)) (PreH10 : (list_within_bound UINT_MOD l2 )) (PreH11 : (n_pre = (Zlength (l1)))) (PreH12 : (n_pre = (Zlength (l2)))) (PreH13 : (0 <= n_pre)) ,
  (UIntArray.full ap_pre n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
|--
  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre )
.

Definition mpn_cmp_return_wit_2 := 
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((Znth n l1 0) > (Znth n l2 0))) (PreH2 : ((Znth n l1 0) <> (Znth n l2 0))) (PreH3 : (n >= 0)) (PreH4 : ((-1) <= n)) (PreH5 : (n < n_pre)) (PreH6 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH7 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH8 : ((last (l1) (1)) >= 1)) (PreH9 : (list_within_bound UINT_MOD l1 )) (PreH10 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH11 : ((last (l2) (1)) >= 1)) (PreH12 : (list_within_bound UINT_MOD l2 )) (PreH13 : (n_pre = (Zlength (l1)))) (PreH14 : (n_pre = (Zlength (l2)))) (PreH15 : (0 <= n_pre)) ,
  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
|--
  “ (val1 > val2) ” 
  &&  “ (1 = 1) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre )
) \/
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((Znth n l1 0) > (Znth n l2 0))) (PreH2 : ((Znth n l1 0) <> (Znth n l2 0))) (PreH3 : (n >= 0)) (PreH4 : ((-1) <= n)) (PreH5 : (n < n_pre)) (PreH6 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH7 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH8 : ((last (l1) (1)) >= 1)) (PreH9 : (list_within_bound UINT_MOD l1 )) (PreH10 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH11 : ((last (l2) (1)) >= 1)) (PreH12 : (list_within_bound UINT_MOD l2 )) (PreH13 : (n_pre = (Zlength (l1)))) (PreH14 : (n_pre = (Zlength (l2)))) (PreH15 : (0 <= n_pre)) ,
  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
|--
  “ (val1 > val2) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre )
).

Definition mpn_cmp_return_wit_2_split_goal_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((Znth n l1 0) > (Znth n l2 0))) (PreH2 : ((Znth n l1 0) <> (Znth n l2 0))) (PreH3 : (n >= 0)) (PreH4 : ((-1) <= n)) (PreH5 : (n < n_pre)) (PreH6 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH7 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH8 : ((last (l1) (1)) >= 1)) (PreH9 : (list_within_bound UINT_MOD l1 )) (PreH10 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH11 : ((last (l2) (1)) >= 1)) (PreH12 : (list_within_bound UINT_MOD l2 )) (PreH13 : (n_pre = (Zlength (l1)))) (PreH14 : (n_pre = (Zlength (l2)))) (PreH15 : (0 <= n_pre)) ,
  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
|--
  “ (val1 > val2) ”
.

Definition mpn_cmp_return_wit_2_split_goal_spatial := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((Znth n l1 0) > (Znth n l2 0))) (PreH2 : ((Znth n l1 0) <> (Znth n l2 0))) (PreH3 : (n >= 0)) (PreH4 : ((-1) <= n)) (PreH5 : (n < n_pre)) (PreH6 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH7 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH8 : ((last (l1) (1)) >= 1)) (PreH9 : (list_within_bound UINT_MOD l1 )) (PreH10 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH11 : ((last (l2) (1)) >= 1)) (PreH12 : (list_within_bound UINT_MOD l2 )) (PreH13 : (n_pre = (Zlength (l1)))) (PreH14 : (n_pre = (Zlength (l2)))) (PreH15 : (0 <= n_pre)) ,
  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
|--
  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre )
.

Definition mpn_cmp_return_wit_3 := 
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((Znth n l1 0) <= (Znth n l2 0))) (PreH2 : ((Znth n l1 0) <> (Znth n l2 0))) (PreH3 : (n >= 0)) (PreH4 : ((-1) <= n)) (PreH5 : (n < n_pre)) (PreH6 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH7 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH8 : ((last (l1) (1)) >= 1)) (PreH9 : (list_within_bound UINT_MOD l1 )) (PreH10 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH11 : ((last (l2) (1)) >= 1)) (PreH12 : (list_within_bound UINT_MOD l2 )) (PreH13 : (n_pre = (Zlength (l1)))) (PreH14 : (n_pre = (Zlength (l2)))) (PreH15 : (0 <= n_pre)) ,
  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
|--
  “ (val1 < val2) ” 
  &&  “ ((-1) = (-1)) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre )
) \/
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((Znth n l1 0) <= (Znth n l2 0))) (PreH2 : ((Znth n l1 0) <> (Znth n l2 0))) (PreH3 : (n >= 0)) (PreH4 : ((-1) <= n)) (PreH5 : (n < n_pre)) (PreH6 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH7 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH8 : ((last (l1) (1)) >= 1)) (PreH9 : (list_within_bound UINT_MOD l1 )) (PreH10 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH11 : ((last (l2) (1)) >= 1)) (PreH12 : (list_within_bound UINT_MOD l2 )) (PreH13 : (n_pre = (Zlength (l1)))) (PreH14 : (n_pre = (Zlength (l2)))) (PreH15 : (0 <= n_pre)) ,
  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
|--
  “ (val1 < val2) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre )
).

Definition mpn_cmp_return_wit_3_split_goal_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((Znth n l1 0) <= (Znth n l2 0))) (PreH2 : ((Znth n l1 0) <> (Znth n l2 0))) (PreH3 : (n >= 0)) (PreH4 : ((-1) <= n)) (PreH5 : (n < n_pre)) (PreH6 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH7 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH8 : ((last (l1) (1)) >= 1)) (PreH9 : (list_within_bound UINT_MOD l1 )) (PreH10 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH11 : ((last (l2) (1)) >= 1)) (PreH12 : (list_within_bound UINT_MOD l2 )) (PreH13 : (n_pre = (Zlength (l1)))) (PreH14 : (n_pre = (Zlength (l2)))) (PreH15 : (0 <= n_pre)) ,
  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
|--
  “ (val1 < val2) ”
.

Definition mpn_cmp_return_wit_3_split_goal_spatial := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((Znth n l1 0) <= (Znth n l2 0))) (PreH2 : ((Znth n l1 0) <> (Znth n l2 0))) (PreH3 : (n >= 0)) (PreH4 : ((-1) <= n)) (PreH5 : (n < n_pre)) (PreH6 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH7 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH8 : ((last (l1) (1)) >= 1)) (PreH9 : (list_within_bound UINT_MOD l1 )) (PreH10 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH11 : ((last (l2) (1)) >= 1)) (PreH12 : (list_within_bound UINT_MOD l2 )) (PreH13 : (n_pre = (Zlength (l1)))) (PreH14 : (n_pre = (Zlength (l2)))) (PreH15 : (0 <= n_pre)) ,
  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
|--
  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre )
.

Definition mpn_cmp_partial_solve_wit_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (PreH1 : (0 <= n_pre)) ,
  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre )
|--
  “ (0 <= n_pre) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre )
.

Definition mpn_cmp_partial_solve_wit_2 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : (n >= 0)) (PreH2 : ((-1) <= n)) (PreH3 : (n < n_pre)) (PreH4 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH5 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH6 : ((last (l1) (1)) >= 1)) (PreH7 : (list_within_bound UINT_MOD l1 )) (PreH8 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH9 : ((last (l2) (1)) >= 1)) (PreH10 : (list_within_bound UINT_MOD l2 )) (PreH11 : (n_pre = (Zlength (l1)))) (PreH12 : (n_pre = (Zlength (l2)))) (PreH13 : (0 <= n_pre)) ,
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
  &&  “ (n_pre = (Zlength (l1))) ” 
  &&  “ (n_pre = (Zlength (l2))) ” 
  &&  “ (0 <= n_pre) ”
  &&  (((ap_pre + (n * sizeof(UINT)))) # UInt  |-> (Znth n l1 0))
  **  (UIntArray.missing_i ap_pre n 0 n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
.

Definition mpn_cmp_partial_solve_wit_3 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : (n >= 0)) (PreH2 : ((-1) <= n)) (PreH3 : (n < n_pre)) (PreH4 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH5 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH6 : ((last (l1) (1)) >= 1)) (PreH7 : (list_within_bound UINT_MOD l1 )) (PreH8 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH9 : ((last (l2) (1)) >= 1)) (PreH10 : (list_within_bound UINT_MOD l2 )) (PreH11 : (n_pre = (Zlength (l1)))) (PreH12 : (n_pre = (Zlength (l2)))) (PreH13 : (0 <= n_pre)) ,
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
  &&  “ (n_pre = (Zlength (l1))) ” 
  &&  “ (n_pre = (Zlength (l2))) ” 
  &&  “ (0 <= n_pre) ”
  &&  (((bp_pre + (n * sizeof(UINT)))) # UInt  |-> (Znth n l2 0))
  **  (UIntArray.missing_i bp_pre n 0 n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
.

Definition mpn_cmp_partial_solve_wit_4 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((Znth n l1 0) <> (Znth n l2 0))) (PreH2 : (n >= 0)) (PreH3 : ((-1) <= n)) (PreH4 : (n < n_pre)) (PreH5 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH6 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH7 : ((last (l1) (1)) >= 1)) (PreH8 : (list_within_bound UINT_MOD l1 )) (PreH9 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH10 : ((last (l2) (1)) >= 1)) (PreH11 : (list_within_bound UINT_MOD l2 )) (PreH12 : (n_pre = (Zlength (l1)))) (PreH13 : (n_pre = (Zlength (l2)))) (PreH14 : (0 <= n_pre)) ,
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
  &&  “ (n_pre = (Zlength (l1))) ” 
  &&  “ (n_pre = (Zlength (l2))) ” 
  &&  “ (0 <= n_pre) ”
  &&  (((ap_pre + (n * sizeof(UINT)))) # UInt  |-> (Znth n l1 0))
  **  (UIntArray.missing_i ap_pre n 0 n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
.

Definition mpn_cmp_partial_solve_wit_5 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) (PreH1 : ((Znth n l1 0) <> (Znth n l2 0))) (PreH2 : (n >= 0)) (PreH3 : ((-1) <= n)) (PreH4 : (n < n_pre)) (PreH5 : ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2)))) (PreH6 : ((list_to_Z (UINT_MOD) (l1)) = val1)) (PreH7 : ((last (l1) (1)) >= 1)) (PreH8 : (list_within_bound UINT_MOD l1 )) (PreH9 : ((list_to_Z (UINT_MOD) (l2)) = val2)) (PreH10 : ((last (l2) (1)) >= 1)) (PreH11 : (list_within_bound UINT_MOD l2 )) (PreH12 : (n_pre = (Zlength (l1)))) (PreH13 : (n_pre = (Zlength (l2)))) (PreH14 : (0 <= n_pre)) ,
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
  &&  “ (n_pre = (Zlength (l1))) ” 
  &&  “ (n_pre = (Zlength (l2))) ” 
  &&  “ (0 <= n_pre) ”
  &&  (((bp_pre + (n * sizeof(UINT)))) # UInt  |-> (Znth n l2 0))
  **  (UIntArray.missing_i bp_pre n 0 n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
.

Definition mpn_cmp_which_implies_wit_1 := 
(
forall (val2: Z) (val1: Z) (n: Z) (ap: Z) (bp: Z) ,
  (mpd_store_Z_compact UINT_MOD ap val1 n )
  **  (mpd_store_Z_compact UINT_MOD bp val2 n )
|--
  EX (l2: (@list Z))  (l1: (@list Z)) ,
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
forall (val2: Z) (val1: Z) (n: Z) (ap: Z) (bp: Z) ,
  (mpd_store_Z_compact UINT_MOD ap val1 n )
  **  (mpd_store_Z_compact UINT_MOD bp val2 n )
|--
  EX (l2: (@list Z))  (l1: (@list Z)) ,
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
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (PreH1 : (an_pre < bn_pre)) (PreH2 : (an_pre <> bn_pre)) (PreH3 : (an_pre >= 0)) (PreH4 : (bn_pre >= 0)) ,
  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition mpn_cmp4_safety_wit_2 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (PreH1 : (an_pre < bn_pre)) (PreH2 : (an_pre <> bn_pre)) (PreH3 : (an_pre >= 0)) (PreH4 : (bn_pre >= 0)) ,
  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_cmp4_safety_wit_3 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (PreH1 : (an_pre >= bn_pre)) (PreH2 : (an_pre <> bn_pre)) (PreH3 : (an_pre >= 0)) (PreH4 : (bn_pre >= 0)) ,
  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_cmp4_return_wit_1 := 
(
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (retval: Z) (PreH1 : (val1 < val2)) (PreH2 : (retval = (-1))) (PreH3 : (an_pre = bn_pre)) (PreH4 : (an_pre >= 0)) (PreH5 : (bn_pre >= 0)) ,
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 an_pre )
|--
  “ (val1 < val2) ” 
  &&  “ (retval = (-1)) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
) \/
(
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (retval: Z) (PreH1 : (val1 < val2)) (PreH2 : (retval = (-1))) (PreH3 : (an_pre = bn_pre)) (PreH4 : (an_pre >= 0)) (PreH5 : (bn_pre >= 0)) ,
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 an_pre )
|--
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
).

Definition mpn_cmp4_return_wit_1_split_goal_spatial := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (retval: Z) (PreH1 : (val1 < val2)) (PreH2 : (retval = (-1))) (PreH3 : (an_pre = bn_pre)) (PreH4 : (an_pre >= 0)) (PreH5 : (bn_pre >= 0)) ,
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 an_pre )
|--
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
.

Definition mpn_cmp4_return_wit_2 := 
(
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (retval: Z) (PreH1 : (val1 = val2)) (PreH2 : (retval = 0)) (PreH3 : (an_pre = bn_pre)) (PreH4 : (an_pre >= 0)) (PreH5 : (bn_pre >= 0)) ,
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 an_pre )
|--
  “ (val1 = val2) ” 
  &&  “ (retval = 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
) \/
(
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (retval: Z) (PreH1 : (val1 = val2)) (PreH2 : (retval = 0)) (PreH3 : (an_pre = bn_pre)) (PreH4 : (an_pre >= 0)) (PreH5 : (bn_pre >= 0)) ,
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 an_pre )
|--
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
).

Definition mpn_cmp4_return_wit_2_split_goal_spatial := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (retval: Z) (PreH1 : (val1 = val2)) (PreH2 : (retval = 0)) (PreH3 : (an_pre = bn_pre)) (PreH4 : (an_pre >= 0)) (PreH5 : (bn_pre >= 0)) ,
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 an_pre )
|--
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
.

Definition mpn_cmp4_return_wit_3 := 
(
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (retval: Z) (PreH1 : (val1 > val2)) (PreH2 : (retval = 1)) (PreH3 : (an_pre = bn_pre)) (PreH4 : (an_pre >= 0)) (PreH5 : (bn_pre >= 0)) ,
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 an_pre )
|--
  “ (val1 > val2) ” 
  &&  “ (retval = 1) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
) \/
(
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (retval: Z) (PreH1 : (val1 > val2)) (PreH2 : (retval = 1)) (PreH3 : (an_pre = bn_pre)) (PreH4 : (an_pre >= 0)) (PreH5 : (bn_pre >= 0)) ,
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 an_pre )
|--
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
).

Definition mpn_cmp4_return_wit_3_split_goal_spatial := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (retval: Z) (PreH1 : (val1 > val2)) (PreH2 : (retval = 1)) (PreH3 : (an_pre = bn_pre)) (PreH4 : (an_pre >= 0)) (PreH5 : (bn_pre >= 0)) ,
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 an_pre )
|--
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
.

Definition mpn_cmp4_return_wit_4 := 
(
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (PreH1 : (an_pre < bn_pre)) (PreH2 : (an_pre <> bn_pre)) (PreH3 : (an_pre >= 0)) (PreH4 : (bn_pre >= 0)) ,
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
|--
  “ (val1 < val2) ” 
  &&  “ ((-1) = (-1)) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
) \/
(
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (PreH1 : (an_pre < bn_pre)) (PreH2 : (an_pre <> bn_pre)) (PreH3 : (an_pre >= 0)) (PreH4 : (bn_pre >= 0)) ,
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
|--
  “ (val1 < val2) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
).

Definition mpn_cmp4_return_wit_4_split_goal_1 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (PreH1 : (an_pre < bn_pre)) (PreH2 : (an_pre <> bn_pre)) (PreH3 : (an_pre >= 0)) (PreH4 : (bn_pre >= 0)) ,
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
|--
  “ (val1 < val2) ”
.

Definition mpn_cmp4_return_wit_4_split_goal_spatial := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (PreH1 : (an_pre < bn_pre)) (PreH2 : (an_pre <> bn_pre)) (PreH3 : (an_pre >= 0)) (PreH4 : (bn_pre >= 0)) ,
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
|--
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
.

Definition mpn_cmp4_return_wit_5 := 
(
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (PreH1 : (an_pre >= bn_pre)) (PreH2 : (an_pre <> bn_pre)) (PreH3 : (an_pre >= 0)) (PreH4 : (bn_pre >= 0)) ,
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
|--
  “ (val1 > val2) ” 
  &&  “ (1 = 1) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
) \/
(
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (PreH1 : (an_pre >= bn_pre)) (PreH2 : (an_pre <> bn_pre)) (PreH3 : (an_pre >= 0)) (PreH4 : (bn_pre >= 0)) ,
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
|--
  “ (val1 > val2) ”
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
).

Definition mpn_cmp4_return_wit_5_split_goal_1 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (PreH1 : (an_pre >= bn_pre)) (PreH2 : (an_pre <> bn_pre)) (PreH3 : (an_pre >= 0)) (PreH4 : (bn_pre >= 0)) ,
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
|--
  “ (val1 > val2) ”
.

Definition mpn_cmp4_return_wit_5_split_goal_spatial := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (PreH1 : (an_pre >= bn_pre)) (PreH2 : (an_pre <> bn_pre)) (PreH3 : (an_pre >= 0)) (PreH4 : (bn_pre >= 0)) ,
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
|--
  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
.

Definition mpn_cmp4_partial_solve_wit_1_pure := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (PreH1 : (an_pre = bn_pre)) (PreH2 : (an_pre >= 0)) (PreH3 : (bn_pre >= 0)) ,
  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
|--
  “ (0 <= an_pre) ”
.

Definition mpn_cmp4_partial_solve_wit_1_aux := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (PreH1 : (an_pre = bn_pre)) (PreH2 : (an_pre >= 0)) (PreH3 : (bn_pre >= 0)) ,
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

(*----- Function mpn_normalized_size -----*)

Definition mpn_normalized_size_safety_wit_1 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (n: Z) (PreH1 : (n >= 0)) (PreH2 : (n <= n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH6 : (list_within_bound UINT_MOD l )) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (0 <= n_pre)) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.full xp_pre n (sublist (0) (n) (l)) )
  **  (UIntArray.undef_seg xp_pre n n_pre )
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_normalized_size_safety_wit_2 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (n: Z) (PreH1 : (n > 0)) (PreH2 : (n >= 0)) (PreH3 : (n <= n_pre)) (PreH4 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH7 : (list_within_bound UINT_MOD l )) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : (0 <= n_pre)) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.full xp_pre n (sublist (0) (n) (l)) )
  **  (UIntArray.undef_seg xp_pre n n_pre )
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
|--
  “ ((n - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n - 1 )) ”
.

Definition mpn_normalized_size_safety_wit_3 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (n: Z) (PreH1 : (n > 0)) (PreH2 : (n >= 0)) (PreH3 : (n <= n_pre)) (PreH4 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH7 : (list_within_bound UINT_MOD l )) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : (0 <= n_pre)) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.full xp_pre n (sublist (0) (n) (l)) )
  **  (UIntArray.undef_seg xp_pre n n_pre )
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_normalized_size_safety_wit_4 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (n: Z) (PreH1 : (n > 0)) (PreH2 : (n >= 0)) (PreH3 : (n <= n_pre)) (PreH4 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH7 : (list_within_bound UINT_MOD l )) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : (0 <= n_pre)) ,
  (UIntArray.full xp_pre n (sublist (0) (n) (l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.undef_seg xp_pre n n_pre )
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_normalized_size_safety_wit_5 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (n: Z) (PreH1 : ((Znth (n - 1 ) (sublist (0) (n) (l)) 0) = 0)) (PreH2 : (n > 0)) (PreH3 : (n >= 0)) (PreH4 : (n <= n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (0 <= n_pre)) ,
  (UIntArray.full xp_pre n (sublist (0) (n) (l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.undef_seg xp_pre n n_pre )
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
|--
  “ ((n - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n - 1 )) ”
.

Definition mpn_normalized_size_entail_wit_1 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (PreH1 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH2 : (list_within_bound UINT_MOD l )) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (0 <= n_pre)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
  **  (UIntArray.full xp_pre n_pre l )
|--
  “ (n_pre <= INT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= n_pre) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
  **  (UIntArray.full xp_pre n_pre l )
.

Definition mpn_normalized_size_entail_wit_2 := 
(
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH3 : (list_within_bound UINT_MOD l )) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= n_pre)) ,
  (UIntArray.full xp_pre n_pre l )
|--
  “ (n_pre >= 0) ” 
  &&  “ (n_pre <= n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (n_pre) (l)))) = val) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= n_pre) ”
  &&  (UIntArray.full xp_pre n_pre (sublist (0) (n_pre) (l)) )
  **  (UIntArray.undef_seg xp_pre n_pre n_pre )
) \/
(
forall (n_pre: Z) (val: Z) (l: (@list Z)) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH3 : (list_within_bound UINT_MOD l )) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= n_pre)) ,
  TT && emp 
|--
  “ ((list_to_Z (UINT_MOD) ((sublist (0) (n_pre) (l)))) = val) ” 
  &&  “ (l = (sublist (0) (n_pre) (l))) ”
  &&  emp
).

Definition mpn_normalized_size_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (val: Z) (l: (@list Z)) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH3 : (list_within_bound UINT_MOD l )) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= n_pre)) ,
  ((list_to_Z (UINT_MOD) ((sublist (0) (n_pre) (l)))) = val)
.

Definition mpn_normalized_size_entail_wit_2_split_goal_2 := 
forall (n_pre: Z) (val: Z) (l: (@list Z)) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH3 : (list_within_bound UINT_MOD l )) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= n_pre)) ,
  (l = (sublist (0) (n_pre) (l)))
.

Definition mpn_normalized_size_entail_wit_3 := 
(
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (n: Z) (PreH1 : ((Znth (n - 1 ) (sublist (0) (n) (l)) 0) = 0)) (PreH2 : (n > 0)) (PreH3 : (n >= 0)) (PreH4 : (n <= n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (0 <= n_pre)) ,
  (UIntArray.full xp_pre n (sublist (0) (n) (l)) )
  **  (UIntArray.undef_seg xp_pre n n_pre )
|--
  “ ((n - 1 ) >= 0) ” 
  &&  “ ((n - 1 ) <= n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((n - 1 )) (l)))) = val) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= n_pre) ”
  &&  (UIntArray.full xp_pre (n - 1 ) (sublist (0) ((n - 1 )) (l)) )
  **  (UIntArray.undef_seg xp_pre (n - 1 ) n_pre )
) \/
(
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (n: Z) (PreH1 : ((Znth (n - 1 ) (sublist (0) (n) (l)) 0) = 0)) (PreH2 : (n > 0)) (PreH3 : (n >= 0)) (PreH4 : (n <= n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (0 <= n_pre)) ,
  (UIntArray.full xp_pre n (sublist (0) (n) (l)) )
  **  (UIntArray.undef_seg xp_pre n n_pre )
|--
  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((n - 1 )) (l)))) = val) ”
  &&  (UIntArray.full xp_pre (n - 1 ) (sublist (0) ((n - 1 )) (l)) )
  **  (UIntArray.undef_seg xp_pre (n - 1 ) n_pre )
).

Definition mpn_normalized_size_entail_wit_3_split_goal_1 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (n: Z) (PreH1 : ((Znth (n - 1 ) (sublist (0) (n) (l)) 0) = 0)) (PreH2 : (n > 0)) (PreH3 : (n >= 0)) (PreH4 : (n <= n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (0 <= n_pre)) ,
  (UIntArray.full xp_pre n (sublist (0) (n) (l)) )
  **  (UIntArray.undef_seg xp_pre n n_pre )
|--
  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((n - 1 )) (l)))) = val) ”
.

Definition mpn_normalized_size_entail_wit_3_split_goal_spatial := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (n: Z) (PreH1 : ((Znth (n - 1 ) (sublist (0) (n) (l)) 0) = 0)) (PreH2 : (n > 0)) (PreH3 : (n >= 0)) (PreH4 : (n <= n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (0 <= n_pre)) ,
  (UIntArray.full xp_pre n (sublist (0) (n) (l)) )
  **  (UIntArray.undef_seg xp_pre n n_pre )
|--
  (UIntArray.full xp_pre (n - 1 ) (sublist (0) ((n - 1 )) (l)) )
  **  (UIntArray.undef_seg xp_pre (n - 1 ) n_pre )
.

Definition mpn_normalized_size_return_wit_1 := 
(
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (n: Z) (PreH1 : (n <= 0)) (PreH2 : (n >= 0)) (PreH3 : (n <= n_pre)) (PreH4 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH7 : (list_within_bound UINT_MOD l )) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : (0 <= n_pre)) ,
  (UIntArray.full xp_pre n (sublist (0) (n) (l)) )
  **  (UIntArray.undef_seg xp_pre n n_pre )
|--
  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ”
  &&  (mpd_store_Z_compact UINT_MOD xp_pre val n )
  **  (UIntArray.undef_seg xp_pre n n_pre )
) \/
(
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (n: Z) (PreH1 : (n <= 0)) (PreH2 : (n >= 0)) (PreH3 : (n <= n_pre)) (PreH4 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH7 : (list_within_bound UINT_MOD l )) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : (0 <= n_pre)) ,
  (UIntArray.full xp_pre n (sublist (0) (n) (l)) )
|--
  (mpd_store_Z_compact UINT_MOD xp_pre val n )
).

Definition mpn_normalized_size_return_wit_1_split_goal_spatial := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (n: Z) (PreH1 : (n <= 0)) (PreH2 : (n >= 0)) (PreH3 : (n <= n_pre)) (PreH4 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH7 : (list_within_bound UINT_MOD l )) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : (0 <= n_pre)) ,
  (UIntArray.full xp_pre n (sublist (0) (n) (l)) )
|--
  (mpd_store_Z_compact UINT_MOD xp_pre val n )
.

Definition mpn_normalized_size_return_wit_2 := 
(
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (n: Z) (PreH1 : ((Znth (n - 1 ) (sublist (0) (n) (l)) 0) <> 0)) (PreH2 : (n > 0)) (PreH3 : (n >= 0)) (PreH4 : (n <= n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (0 <= n_pre)) ,
  (UIntArray.full xp_pre n (sublist (0) (n) (l)) )
  **  (UIntArray.undef_seg xp_pre n n_pre )
|--
  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ”
  &&  (mpd_store_Z_compact UINT_MOD xp_pre val n )
  **  (UIntArray.undef_seg xp_pre n n_pre )
) \/
(
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (n: Z) (PreH1 : ((Znth (n - 1 ) (sublist (0) (n) (l)) 0) <> 0)) (PreH2 : (n > 0)) (PreH3 : (n >= 0)) (PreH4 : (n <= n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (0 <= n_pre)) ,
  (UIntArray.full xp_pre n (sublist (0) (n) (l)) )
|--
  (mpd_store_Z_compact UINT_MOD xp_pre val n )
).

Definition mpn_normalized_size_return_wit_2_split_goal_spatial := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (n: Z) (PreH1 : ((Znth (n - 1 ) (sublist (0) (n) (l)) 0) <> 0)) (PreH2 : (n > 0)) (PreH3 : (n >= 0)) (PreH4 : (n <= n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (0 <= n_pre)) ,
  (UIntArray.full xp_pre n (sublist (0) (n) (l)) )
|--
  (mpd_store_Z_compact UINT_MOD xp_pre val n )
.

Definition mpn_normalized_size_partial_solve_wit_1 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (PreH1 : (0 <= n_pre)) ,
  (mpd_store_Z UINT_MOD xp_pre val n_pre )
|--
  “ (0 <= n_pre) ”
  &&  (mpd_store_Z UINT_MOD xp_pre val n_pre )
.

Definition mpn_normalized_size_partial_solve_wit_2 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (n: Z) (PreH1 : (n > 0)) (PreH2 : (n >= 0)) (PreH3 : (n <= n_pre)) (PreH4 : ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH7 : (list_within_bound UINT_MOD l )) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : (0 <= n_pre)) ,
  (UIntArray.full xp_pre n (sublist (0) (n) (l)) )
  **  (UIntArray.undef_seg xp_pre n n_pre )
|--
  “ (n > 0) ” 
  &&  “ (n >= 0) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= n_pre) ”
  &&  (((xp_pre + ((n - 1 ) * sizeof(UINT)))) # UInt  |-> (Znth (n - 1 ) (sublist (0) (n) (l)) 0))
  **  (UIntArray.missing_i xp_pre (n - 1 ) 0 n (sublist (0) (n) (l)) )
  **  (UIntArray.undef_seg xp_pre n n_pre )
.

Definition mpn_normalized_size_which_implies_wit_1 := 
(
forall (val: Z) (n: Z) (xp: Z) ,
  (mpd_store_Z UINT_MOD xp val n )
|--
  EX (l: (@list Z)) ,
  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n) ”
  &&  (UIntArray.full xp n l )
) \/
(
forall (val: Z) (n: Z) (xp: Z) ,
  (mpd_store_Z UINT_MOD xp val n )
|--
  EX (l: (@list Z)) ,
  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n) ”
  &&  (UIntArray.full xp n l )
).

(*----- Function mpn_add_1 -----*)

Definition mpn_add_1_safety_wit_1 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH3 : (list_within_bound UINT_MOD l )) (PreH4 : (n_pre > 0)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre <= UINT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.full ap_pre n_pre l )
  **  ((( &( "b" ) )) # UInt  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_add_1_safety_wit_2 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (PreH1 : ((unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)) >= b_pre)) (PreH2 : ((Zlength (l)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH4 : (list_within_bound UINT_MOD l )) (PreH5 : (n_pre > 0)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= UINT_MAX)) ,
  (((rp_pre + (0 * sizeof(UINT)))) # UInt  |-> (unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)))
  **  (UIntArray.undef_seg rp_pre 1 n_pre )
  **  (UIntArray.full ap_pre n_pre l )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)))
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "b" ) )) # UInt  |-> 0)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  “ ((0 + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (0 + 1 )) ”
.

Definition mpn_add_1_safety_wit_3 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (PreH1 : ((unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)) < b_pre)) (PreH2 : ((Zlength (l)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH4 : (list_within_bound UINT_MOD l )) (PreH5 : (n_pre > 0)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= UINT_MAX)) ,
  (((rp_pre + (0 * sizeof(UINT)))) # UInt  |-> (unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)))
  **  (UIntArray.undef_seg rp_pre 1 n_pre )
  **  (UIntArray.full ap_pre n_pre l )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)))
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "b" ) )) # UInt  |-> 1)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  “ ((0 + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (0 + 1 )) ”
.

Definition mpn_add_1_safety_wit_4 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (l': (@list Z)) (val1: Z) (val2: Z) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) >= b)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b < UINT_MOD)) (PreH7 : ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre ))) (PreH8 : ((Zlength (l')) = i)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1)) (PreH10 : ((list_to_Z (UINT_MOD) (l')) = val2)) (PreH11 : (list_within_bound UINT_MOD l' )) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH14 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.full rp_pre (i + 1 ) (app (l') ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((Znth i l 0) + b )) (32)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "b" ) )) # UInt  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_add_1_safety_wit_5 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (l': (@list Z)) (val1: Z) (val2: Z) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) < b)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b < UINT_MOD)) (PreH7 : ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre ))) (PreH8 : ((Zlength (l')) = i)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1)) (PreH10 : ((list_to_Z (UINT_MOD) (l')) = val2)) (PreH11 : (list_within_bound UINT_MOD l' )) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH14 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.full rp_pre (i + 1 ) (app (l') ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((Znth i l 0) + b )) (32)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "b" ) )) # UInt  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_add_1_entail_wit_1_1 := 
(
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (l'_2: (@list Z)) (val1_2: Z) (val2_2: Z) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) >= b)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b < UINT_MOD)) (PreH7 : ((val2_2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1_2 + b_pre ))) (PreH8 : ((Zlength (l'_2)) = i)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1_2)) (PreH10 : ((list_to_Z (UINT_MOD) (l'_2)) = val2_2)) (PreH11 : (list_within_bound UINT_MOD l'_2 )) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH14 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.full rp_pre (i + 1 ) (app (l'_2) ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l )
|--
  EX (l': (@list Z))  (val1: Z)  (val2: Z) ,
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < UINT_MOD) ” 
  &&  “ ((val2 + (0 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val1 + b_pre )) ” 
  &&  “ ((Zlength (l')) = (i + 1 )) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.full rp_pre (i + 1 ) l' )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
) \/
(
forall (b_pre: Z) (n_pre: Z) (val: Z) (l: (@list Z)) (l'_2: (@list Z)) (val1_2: Z) (val2_2: Z) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) >= b)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b < UINT_MOD)) (PreH7 : ((val2_2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1_2 + b_pre ))) (PreH8 : ((Zlength (l'_2)) = i)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1_2)) (PreH10 : ((list_to_Z (UINT_MOD) (l'_2)) = val2_2)) (PreH11 : (list_within_bound UINT_MOD l'_2 )) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH14 : (list_within_bound UINT_MOD l )) ,
  TT && emp 
|--
  “ (list_within_bound UINT_MOD (app (l'_2) ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((app (l'_2) ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) ((@nil Z))))))) = (i + 1 )) ” 
  &&  “ (((list_to_Z (UINT_MOD) ((app (l'_2) ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) ((@nil Z))))))) + (0 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) + b_pre )) ”
  &&  emp
).

Definition mpn_add_1_entail_wit_1_1_split_goal_1 := 
forall (b_pre: Z) (n_pre: Z) (val: Z) (l: (@list Z)) (l'_2: (@list Z)) (val1_2: Z) (val2_2: Z) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) >= b)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b < UINT_MOD)) (PreH7 : ((val2_2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1_2 + b_pre ))) (PreH8 : ((Zlength (l'_2)) = i)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1_2)) (PreH10 : ((list_to_Z (UINT_MOD) (l'_2)) = val2_2)) (PreH11 : (list_within_bound UINT_MOD l'_2 )) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH14 : (list_within_bound UINT_MOD l )) ,
  (list_within_bound UINT_MOD (app (l'_2) ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) ((@nil Z))))) )
.

Definition mpn_add_1_entail_wit_1_1_split_goal_2 := 
forall (b_pre: Z) (n_pre: Z) (val: Z) (l: (@list Z)) (l'_2: (@list Z)) (val1_2: Z) (val2_2: Z) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) >= b)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b < UINT_MOD)) (PreH7 : ((val2_2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1_2 + b_pre ))) (PreH8 : ((Zlength (l'_2)) = i)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1_2)) (PreH10 : ((list_to_Z (UINT_MOD) (l'_2)) = val2_2)) (PreH11 : (list_within_bound UINT_MOD l'_2 )) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH14 : (list_within_bound UINT_MOD l )) ,
  ((Zlength ((app (l'_2) ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) ((@nil Z))))))) = (i + 1 ))
.

Definition mpn_add_1_entail_wit_1_1_split_goal_3 := 
forall (b_pre: Z) (n_pre: Z) (val: Z) (l: (@list Z)) (l'_2: (@list Z)) (val1_2: Z) (val2_2: Z) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) >= b)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b < UINT_MOD)) (PreH7 : ((val2_2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1_2 + b_pre ))) (PreH8 : ((Zlength (l'_2)) = i)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1_2)) (PreH10 : ((list_to_Z (UINT_MOD) (l'_2)) = val2_2)) (PreH11 : (list_within_bound UINT_MOD l'_2 )) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH14 : (list_within_bound UINT_MOD l )) ,
  (((list_to_Z (UINT_MOD) ((app (l'_2) ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) ((@nil Z))))))) + (0 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) + b_pre ))
.

Definition mpn_add_1_entail_wit_1_2 := 
(
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (l'_2: (@list Z)) (val1_2: Z) (val2_2: Z) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) < b)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b < UINT_MOD)) (PreH7 : ((val2_2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1_2 + b_pre ))) (PreH8 : ((Zlength (l'_2)) = i)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1_2)) (PreH10 : ((list_to_Z (UINT_MOD) (l'_2)) = val2_2)) (PreH11 : (list_within_bound UINT_MOD l'_2 )) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH14 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.full rp_pre (i + 1 ) (app (l'_2) ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l )
|--
  EX (l': (@list Z))  (val1: Z)  (val2: Z) ,
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 < UINT_MOD) ” 
  &&  “ ((val2 + (1 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val1 + b_pre )) ” 
  &&  “ ((Zlength (l')) = (i + 1 )) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.full rp_pre (i + 1 ) l' )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
) \/
(
forall (b_pre: Z) (n_pre: Z) (val: Z) (l: (@list Z)) (l'_2: (@list Z)) (val1_2: Z) (val2_2: Z) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) < b)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b < UINT_MOD)) (PreH7 : ((val2_2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1_2 + b_pre ))) (PreH8 : ((Zlength (l'_2)) = i)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1_2)) (PreH10 : ((list_to_Z (UINT_MOD) (l'_2)) = val2_2)) (PreH11 : (list_within_bound UINT_MOD l'_2 )) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH14 : (list_within_bound UINT_MOD l )) ,
  TT && emp 
|--
  “ (list_within_bound UINT_MOD (app (l'_2) ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((app (l'_2) ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) ((@nil Z))))))) = (i + 1 )) ” 
  &&  “ (((list_to_Z (UINT_MOD) ((app (l'_2) ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) ((@nil Z))))))) + (1 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) + b_pre )) ” 
  &&  “ (1 < UINT_MOD) ”
  &&  emp
).

Definition mpn_add_1_entail_wit_1_2_split_goal_1 := 
forall (b_pre: Z) (n_pre: Z) (val: Z) (l: (@list Z)) (l'_2: (@list Z)) (val1_2: Z) (val2_2: Z) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) < b)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b < UINT_MOD)) (PreH7 : ((val2_2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1_2 + b_pre ))) (PreH8 : ((Zlength (l'_2)) = i)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1_2)) (PreH10 : ((list_to_Z (UINT_MOD) (l'_2)) = val2_2)) (PreH11 : (list_within_bound UINT_MOD l'_2 )) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH14 : (list_within_bound UINT_MOD l )) ,
  (list_within_bound UINT_MOD (app (l'_2) ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) ((@nil Z))))) )
.

Definition mpn_add_1_entail_wit_1_2_split_goal_2 := 
forall (b_pre: Z) (n_pre: Z) (val: Z) (l: (@list Z)) (l'_2: (@list Z)) (val1_2: Z) (val2_2: Z) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) < b)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b < UINT_MOD)) (PreH7 : ((val2_2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1_2 + b_pre ))) (PreH8 : ((Zlength (l'_2)) = i)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1_2)) (PreH10 : ((list_to_Z (UINT_MOD) (l'_2)) = val2_2)) (PreH11 : (list_within_bound UINT_MOD l'_2 )) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH14 : (list_within_bound UINT_MOD l )) ,
  ((Zlength ((app (l'_2) ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) ((@nil Z))))))) = (i + 1 ))
.

Definition mpn_add_1_entail_wit_1_2_split_goal_3 := 
forall (b_pre: Z) (n_pre: Z) (val: Z) (l: (@list Z)) (l'_2: (@list Z)) (val1_2: Z) (val2_2: Z) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) < b)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b < UINT_MOD)) (PreH7 : ((val2_2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1_2 + b_pre ))) (PreH8 : ((Zlength (l'_2)) = i)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1_2)) (PreH10 : ((list_to_Z (UINT_MOD) (l'_2)) = val2_2)) (PreH11 : (list_within_bound UINT_MOD l'_2 )) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH14 : (list_within_bound UINT_MOD l )) ,
  (((list_to_Z (UINT_MOD) ((app (l'_2) ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) ((@nil Z))))))) + (1 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) + b_pre ))
.

Definition mpn_add_1_entail_wit_1_2_split_goal_4 := 
forall (b_pre: Z) (n_pre: Z) (val: Z) (l: (@list Z)) (l'_2: (@list Z)) (val1_2: Z) (val2_2: Z) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) < b)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b < UINT_MOD)) (PreH7 : ((val2_2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1_2 + b_pre ))) (PreH8 : ((Zlength (l'_2)) = i)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1_2)) (PreH10 : ((list_to_Z (UINT_MOD) (l'_2)) = val2_2)) (PreH11 : (list_within_bound UINT_MOD l'_2 )) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH14 : (list_within_bound UINT_MOD l )) ,
  (1 < UINT_MOD)
.

Definition mpn_add_1_entail_wit_2_1 := 
(
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (PreH1 : ((unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)) >= b_pre)) (PreH2 : ((Zlength (l)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH4 : (list_within_bound UINT_MOD l )) (PreH5 : (n_pre > 0)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= UINT_MAX)) ,
  (((rp_pre + (0 * sizeof(UINT)))) # UInt  |-> (unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)))
  **  (UIntArray.undef_seg rp_pre 1 n_pre )
  **  (UIntArray.full ap_pre n_pre l )
|--
  EX (l': (@list Z))  (val1: Z)  (val2: Z) ,
  “ (1 <= (0 + 1 )) ” 
  &&  “ ((0 + 1 ) <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < UINT_MOD) ” 
  &&  “ ((val2 + (0 * (Z.pow (UINT_MOD) ((0 + 1 ))) ) ) = (val1 + b_pre )) ” 
  &&  “ ((Zlength (l')) = (0 + 1 )) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((0 + 1 )) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.full rp_pre (0 + 1 ) l' )
  **  (UIntArray.undef_seg rp_pre (0 + 1 ) n_pre )
) \/
(
forall (b_pre: Z) (n_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (PreH1 : ((unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)) <= UINT_MAX)) (PreH2 : ((unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)) >= 0)) (PreH3 : ((unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)) >= b_pre)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH6 : (list_within_bound UINT_MOD l )) (PreH7 : (n_pre > 0)) (PreH8 : (0 <= b_pre)) (PreH9 : (b_pre <= UINT_MAX)) ,
  (((rp_pre + (0 * sizeof(UINT)))) # UInt  |-> (unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)))
|--
  EX (l': (@list Z)) ,
  “ (1 <= (0 + 1 )) ” 
  &&  “ ((0 + 1 ) <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < UINT_MOD) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l')) + (0 * (Z.pow (UINT_MOD) ((0 + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((0 + 1 )) (l)))) + b_pre )) ” 
  &&  “ ((Zlength (l')) = (0 + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full rp_pre (0 + 1 ) l' )
).

Definition mpn_add_1_entail_wit_2_2 := 
(
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (PreH1 : ((unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)) < b_pre)) (PreH2 : ((Zlength (l)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH4 : (list_within_bound UINT_MOD l )) (PreH5 : (n_pre > 0)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= UINT_MAX)) ,
  (((rp_pre + (0 * sizeof(UINT)))) # UInt  |-> (unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)))
  **  (UIntArray.undef_seg rp_pre 1 n_pre )
  **  (UIntArray.full ap_pre n_pre l )
|--
  EX (l': (@list Z))  (val1: Z)  (val2: Z) ,
  “ (1 <= (0 + 1 )) ” 
  &&  “ ((0 + 1 ) <= n_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 < UINT_MOD) ” 
  &&  “ ((val2 + (1 * (Z.pow (UINT_MOD) ((0 + 1 ))) ) ) = (val1 + b_pre )) ” 
  &&  “ ((Zlength (l')) = (0 + 1 )) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((0 + 1 )) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.full rp_pre (0 + 1 ) l' )
  **  (UIntArray.undef_seg rp_pre (0 + 1 ) n_pre )
) \/
(
forall (b_pre: Z) (n_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (PreH1 : ((unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)) <= UINT_MAX)) (PreH2 : ((unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)) >= 0)) (PreH3 : ((unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)) < b_pre)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH6 : (list_within_bound UINT_MOD l )) (PreH7 : (n_pre > 0)) (PreH8 : (0 <= b_pre)) (PreH9 : (b_pre <= UINT_MAX)) ,
  (((rp_pre + (0 * sizeof(UINT)))) # UInt  |-> (unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)))
|--
  EX (l': (@list Z)) ,
  “ (1 <= (0 + 1 )) ” 
  &&  “ ((0 + 1 ) <= n_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 < UINT_MOD) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l')) + (1 * (Z.pow (UINT_MOD) ((0 + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((0 + 1 )) (l)))) + b_pre )) ” 
  &&  “ ((Zlength (l')) = (0 + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full rp_pre (0 + 1 ) l' )
).

Definition mpn_add_1_return_wit_1 := 
(
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (l': (@list Z)) (val1: Z) (val2: Z) (b: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= b)) (PreH5 : (b < UINT_MOD)) (PreH6 : ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre ))) (PreH7 : ((Zlength (l')) = i)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1)) (PreH9 : ((list_to_Z (UINT_MOD) (l')) = val2)) (PreH10 : (list_within_bound UINT_MOD l' )) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH13 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.full rp_pre i l' )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  EX (val': Z) ,
  “ ((val' + (b * (Z.pow (UINT_MOD) (n_pre)) ) ) = (val + b_pre )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val n_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val' n_pre )
) \/
(
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (l': (@list Z)) (val1: Z) (val2: Z) (b: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= b)) (PreH5 : (b < UINT_MOD)) (PreH6 : ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre ))) (PreH7 : ((Zlength (l')) = i)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1)) (PreH9 : ((list_to_Z (UINT_MOD) (l')) = val2)) (PreH10 : (list_within_bound UINT_MOD l' )) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH13 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.full rp_pre i l' )
|--
  EX (val': Z) ,
  “ ((val' + (b * (Z.pow (UINT_MOD) (n_pre)) ) ) = (val + b_pre )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val n_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val' n_pre )
).

Definition mpn_add_1_partial_solve_wit_1 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (PreH1 : (n_pre > 0)) (PreH2 : (0 <= b_pre)) (PreH3 : (b_pre <= UINT_MAX)) ,
  (mpd_store_Z UINT_MOD ap_pre val n_pre )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (n_pre > 0) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= UINT_MAX) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val n_pre )
  **  (UIntArray.undef_full rp_pre n_pre )
.

Definition mpn_add_1_partial_solve_wit_2 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH3 : (list_within_bound UINT_MOD l )) (PreH4 : (n_pre > 0)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre <= UINT_MAX)) ,
  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= UINT_MAX) ”
  &&  (((ap_pre + (0 * sizeof(UINT)))) # UInt  |-> (Znth 0 l 0))
  **  (UIntArray.missing_i ap_pre 0 0 n_pre l )
  **  (UIntArray.undef_full rp_pre n_pre )
.

Definition mpn_add_1_partial_solve_wit_3 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (PreH1 : ((unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)) >= b_pre)) (PreH2 : ((Zlength (l)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH4 : (list_within_bound UINT_MOD l )) (PreH5 : (n_pre > 0)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= UINT_MAX)) ,
  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ ((unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)) >= b_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= UINT_MAX) ”
  &&  (((rp_pre + (0 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre 1 n_pre )
  **  (UIntArray.full ap_pre n_pre l )
.

Definition mpn_add_1_partial_solve_wit_4 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (PreH1 : ((unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)) < b_pre)) (PreH2 : ((Zlength (l)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH4 : (list_within_bound UINT_MOD l )) (PreH5 : (n_pre > 0)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= UINT_MAX)) ,
  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ ((unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)) < b_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= UINT_MAX) ”
  &&  (((rp_pre + (0 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre 1 n_pre )
  **  (UIntArray.full ap_pre n_pre l )
.

Definition mpn_add_1_partial_solve_wit_5 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (l': (@list Z)) (val1: Z) (val2: Z) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) >= b)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b < UINT_MOD)) (PreH7 : ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre ))) (PreH8 : ((Zlength (l')) = i)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1)) (PreH10 : ((list_to_Z (UINT_MOD) (l')) = val2)) (PreH11 : (list_within_bound UINT_MOD l' )) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH14 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.full rp_pre i l' )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) >= b) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b < UINT_MOD) ” 
  &&  “ ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) ” 
  &&  “ ((Zlength (l')) = i) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.full rp_pre i l' )
.

Definition mpn_add_1_partial_solve_wit_6 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (l': (@list Z)) (val1: Z) (val2: Z) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) < b)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b < UINT_MOD)) (PreH7 : ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre ))) (PreH8 : ((Zlength (l')) = i)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1)) (PreH10 : ((list_to_Z (UINT_MOD) (l')) = val2)) (PreH11 : (list_within_bound UINT_MOD l' )) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH14 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.full rp_pre i l' )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) < b) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b < UINT_MOD) ” 
  &&  “ ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) ” 
  &&  “ ((Zlength (l')) = i) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.full rp_pre i l' )
.

Definition mpn_add_1_partial_solve_wit_7 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (l': (@list Z)) (val1: Z) (val2: Z) (b: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= b)) (PreH5 : (b < UINT_MOD)) (PreH6 : ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre ))) (PreH7 : ((Zlength (l')) = i)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1)) (PreH9 : ((list_to_Z (UINT_MOD) (l')) = val2)) (PreH10 : (list_within_bound UINT_MOD l' )) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH13 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.full rp_pre i l' )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b < UINT_MOD) ” 
  &&  “ ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) ” 
  &&  “ ((Zlength (l')) = i) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (((ap_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth i l 0))
  **  (UIntArray.missing_i ap_pre i 0 n_pre l )
  **  (UIntArray.full rp_pre i l' )
  **  (UIntArray.undef_seg rp_pre i n_pre )
.

Definition mpn_add_1_which_implies_wit_1 := 
(
forall (val: Z) (n: Z) (ap: Z) ,
  (mpd_store_Z UINT_MOD ap val n )
|--
  EX (l: (@list Z)) ,
  “ ((Zlength (l)) = n) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full ap n l )
) \/
(
forall (val: Z) (n: Z) (ap: Z) ,
  (mpd_store_Z UINT_MOD ap val n )
|--
  EX (l: (@list Z)) ,
  “ ((Zlength (l)) = n) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full ap n l )
).

(*----- Function mpn_add_n -----*)

Definition mpn_add_n_safety_wit_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_b: (@list Z)) (l_a: (@list Z)) (PreH1 : ((Zlength (l_a)) = n_pre)) (PreH2 : ((Zlength (l_b)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH4 : (list_within_bound UINT_MOD l_a )) (PreH5 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH6 : (list_within_bound UINT_MOD l_b )) (PreH7 : (n_pre >= 0)) ,
  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.full bp_pre n_pre l_b )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_add_n_safety_wit_2 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_b: (@list Z)) (l_a: (@list Z)) (PreH1 : ((Zlength (l_a)) = n_pre)) (PreH2 : ((Zlength (l_b)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH4 : (list_within_bound UINT_MOD l_a )) (PreH5 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH6 : (list_within_bound UINT_MOD l_b )) (PreH7 : (n_pre >= 0)) ,
  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.full bp_pre n_pre l_b )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_add_n_safety_wit_3 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH11 : (list_within_bound UINT_MOD l_r )) (PreH12 : ((Zlength (l_r)) = i)) (PreH13 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH14 : ((Zlength (l_a)) = n_pre)) (PreH15 : ((Zlength (l_b)) = n_pre)) (PreH16 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH17 : (list_within_bound UINT_MOD l_a )) (PreH18 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH19 : (list_within_bound UINT_MOD l_b )) (PreH20 : (n_pre >= 0)) ,
  (UIntArray.full rp_pre (i + 1 ) (app (l_r) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth i l_b 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth i l_a 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # UInt  |-> (0 + 0 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_add_n_safety_wit_4 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH11 : (list_within_bound UINT_MOD l_r )) (PreH12 : ((Zlength (l_r)) = i)) (PreH13 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH14 : ((Zlength (l_a)) = n_pre)) (PreH15 : ((Zlength (l_b)) = n_pre)) (PreH16 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH17 : (list_within_bound UINT_MOD l_a )) (PreH18 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH19 : (list_within_bound UINT_MOD l_b )) (PreH20 : (n_pre >= 0)) ,
  (UIntArray.full rp_pre (i + 1 ) (app (l_r) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth i l_b 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth i l_a 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # UInt  |-> (0 + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_add_n_safety_wit_5 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH11 : (list_within_bound UINT_MOD l_r )) (PreH12 : ((Zlength (l_r)) = i)) (PreH13 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH14 : ((Zlength (l_a)) = n_pre)) (PreH15 : ((Zlength (l_b)) = n_pre)) (PreH16 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH17 : (list_within_bound UINT_MOD l_a )) (PreH18 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH19 : (list_within_bound UINT_MOD l_b )) (PreH20 : (n_pre >= 0)) ,
  (UIntArray.full rp_pre (i + 1 ) (app (l_r) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth i l_b 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth i l_a 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # UInt  |-> (1 + 0 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_add_n_safety_wit_6 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH11 : (list_within_bound UINT_MOD l_r )) (PreH12 : ((Zlength (l_r)) = i)) (PreH13 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH14 : ((Zlength (l_a)) = n_pre)) (PreH15 : ((Zlength (l_b)) = n_pre)) (PreH16 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH17 : (list_within_bound UINT_MOD l_a )) (PreH18 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH19 : (list_within_bound UINT_MOD l_b )) (PreH20 : (n_pre >= 0)) ,
  (UIntArray.full rp_pre (i + 1 ) (app (l_r) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth i l_b 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth i l_a 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # UInt  |-> (1 + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_add_n_entail_wit_1 := 
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (PreH1 : ((Zlength (l_a)) = n_pre)) (PreH2 : ((Zlength (l_b)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH4 : (list_within_bound UINT_MOD l_a )) (PreH5 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH6 : (list_within_bound UINT_MOD l_b )) (PreH7 : (n_pre >= 0)) ,
  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  EX (val_r: Z)  (l_r: (@list Z))  (val_b_prefix: Z)  (val_a_prefix: Z) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (0) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (0) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((Zlength (l_r)) = 0) ” 
  &&  “ ((val_r + (0 * (Z.pow (UINT_MOD) (0)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.full rp_pre 0 l_r )
  **  (UIntArray.undef_seg rp_pre 0 n_pre )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
) \/
(
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (PreH1 : ((Zlength (l_a)) = n_pre)) (PreH2 : ((Zlength (l_b)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH4 : (list_within_bound UINT_MOD l_a )) (PreH5 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH6 : (list_within_bound UINT_MOD l_b )) (PreH7 : (n_pre >= 0)) ,
  TT && emp 
|--
  “ (((list_to_Z (UINT_MOD) ((@nil Z))) + (0 * (Z.pow (UINT_MOD) (0)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (0) (l_a)))) + (list_to_Z (UINT_MOD) ((sublist (0) (0) (l_b)))) )) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ (list_within_bound UINT_MOD (@nil Z) ) ”
  &&  emp
).

Definition mpn_add_n_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (PreH1 : ((Zlength (l_a)) = n_pre)) (PreH2 : ((Zlength (l_b)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH4 : (list_within_bound UINT_MOD l_a )) (PreH5 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH6 : (list_within_bound UINT_MOD l_b )) (PreH7 : (n_pre >= 0)) ,
  (((list_to_Z (UINT_MOD) ((@nil Z))) + (0 * (Z.pow (UINT_MOD) (0)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (0) (l_a)))) + (list_to_Z (UINT_MOD) ((sublist (0) (0) (l_b)))) ))
.

Definition mpn_add_n_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (PreH1 : ((Zlength (l_a)) = n_pre)) (PreH2 : ((Zlength (l_b)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH4 : (list_within_bound UINT_MOD l_a )) (PreH5 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH6 : (list_within_bound UINT_MOD l_b )) (PreH7 : (n_pre >= 0)) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition mpn_add_n_entail_wit_1_split_goal_3 := 
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (PreH1 : ((Zlength (l_a)) = n_pre)) (PreH2 : ((Zlength (l_b)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH4 : (list_within_bound UINT_MOD l_a )) (PreH5 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH6 : (list_within_bound UINT_MOD l_b )) (PreH7 : (n_pre >= 0)) ,
  (list_within_bound UINT_MOD (@nil Z) )
.

Definition mpn_add_n_entail_wit_2_1 := 
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH11 : (list_within_bound UINT_MOD l_r_2 )) (PreH12 : ((Zlength (l_r_2)) = i)) (PreH13 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH14 : ((Zlength (l_a)) = n_pre)) (PreH15 : ((Zlength (l_b)) = n_pre)) (PreH16 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH17 : (list_within_bound UINT_MOD l_a )) (PreH18 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH19 : (list_within_bound UINT_MOD l_b )) (PreH20 : (n_pre >= 0)) ,
  (UIntArray.full rp_pre (i + 1 ) (app (l_r_2) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
|--
  EX (val_r: Z)  (l_r: (@list Z))  (val_b_prefix: Z)  (val_a_prefix: Z) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (0 + 0 )) ” 
  &&  “ ((0 + 0 ) <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((Zlength (l_r)) = (i + 1 )) ” 
  &&  “ ((val_r + ((0 + 0 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.full rp_pre (i + 1 ) l_r )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
) \/
(
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH11 : (list_within_bound UINT_MOD l_r_2 )) (PreH12 : ((Zlength (l_r_2)) = i)) (PreH13 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH14 : ((Zlength (l_a)) = n_pre)) (PreH15 : ((Zlength (l_b)) = n_pre)) (PreH16 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH17 : (list_within_bound UINT_MOD l_a )) (PreH18 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH19 : (list_within_bound UINT_MOD l_b )) (PreH20 : (n_pre >= 0)) ,
  TT && emp 
|--
  “ (((list_to_Z (UINT_MOD) ((app (l_r_2) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((@nil Z))))))) + ((0 + 0 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) + (list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) )) ” 
  &&  “ ((Zlength ((app (l_r_2) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((@nil Z))))))) = (i + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD (app (l_r_2) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((@nil Z))))) ) ”
  &&  emp
).

Definition mpn_add_n_entail_wit_2_1_split_goal_1 := 
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH11 : (list_within_bound UINT_MOD l_r_2 )) (PreH12 : ((Zlength (l_r_2)) = i)) (PreH13 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH14 : ((Zlength (l_a)) = n_pre)) (PreH15 : ((Zlength (l_b)) = n_pre)) (PreH16 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH17 : (list_within_bound UINT_MOD l_a )) (PreH18 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH19 : (list_within_bound UINT_MOD l_b )) (PreH20 : (n_pre >= 0)) ,
  (((list_to_Z (UINT_MOD) ((app (l_r_2) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((@nil Z))))))) + ((0 + 0 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) + (list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) ))
.

Definition mpn_add_n_entail_wit_2_1_split_goal_2 := 
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH11 : (list_within_bound UINT_MOD l_r_2 )) (PreH12 : ((Zlength (l_r_2)) = i)) (PreH13 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH14 : ((Zlength (l_a)) = n_pre)) (PreH15 : ((Zlength (l_b)) = n_pre)) (PreH16 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH17 : (list_within_bound UINT_MOD l_a )) (PreH18 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH19 : (list_within_bound UINT_MOD l_b )) (PreH20 : (n_pre >= 0)) ,
  ((Zlength ((app (l_r_2) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((@nil Z))))))) = (i + 1 ))
.

Definition mpn_add_n_entail_wit_2_1_split_goal_3 := 
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH11 : (list_within_bound UINT_MOD l_r_2 )) (PreH12 : ((Zlength (l_r_2)) = i)) (PreH13 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH14 : ((Zlength (l_a)) = n_pre)) (PreH15 : ((Zlength (l_b)) = n_pre)) (PreH16 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH17 : (list_within_bound UINT_MOD l_a )) (PreH18 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH19 : (list_within_bound UINT_MOD l_b )) (PreH20 : (n_pre >= 0)) ,
  (list_within_bound UINT_MOD (app (l_r_2) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((@nil Z))))) )
.

Definition mpn_add_n_entail_wit_2_2 := 
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH11 : (list_within_bound UINT_MOD l_r_2 )) (PreH12 : ((Zlength (l_r_2)) = i)) (PreH13 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH14 : ((Zlength (l_a)) = n_pre)) (PreH15 : ((Zlength (l_b)) = n_pre)) (PreH16 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH17 : (list_within_bound UINT_MOD l_a )) (PreH18 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH19 : (list_within_bound UINT_MOD l_b )) (PreH20 : (n_pre >= 0)) ,
  (UIntArray.full rp_pre (i + 1 ) (app (l_r_2) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
|--
  EX (val_r: Z)  (l_r: (@list Z))  (val_b_prefix: Z)  (val_a_prefix: Z) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (0 + 1 )) ” 
  &&  “ ((0 + 1 ) <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((Zlength (l_r)) = (i + 1 )) ” 
  &&  “ ((val_r + ((0 + 1 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.full rp_pre (i + 1 ) l_r )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
) \/
(
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH11 : (list_within_bound UINT_MOD l_r_2 )) (PreH12 : ((Zlength (l_r_2)) = i)) (PreH13 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH14 : ((Zlength (l_a)) = n_pre)) (PreH15 : ((Zlength (l_b)) = n_pre)) (PreH16 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH17 : (list_within_bound UINT_MOD l_a )) (PreH18 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH19 : (list_within_bound UINT_MOD l_b )) (PreH20 : (n_pre >= 0)) ,
  TT && emp 
|--
  “ (((list_to_Z (UINT_MOD) ((app (l_r_2) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((@nil Z))))))) + ((0 + 1 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) + (list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) )) ” 
  &&  “ ((Zlength ((app (l_r_2) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((@nil Z))))))) = (i + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD (app (l_r_2) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((@nil Z))))) ) ”
  &&  emp
).

Definition mpn_add_n_entail_wit_2_2_split_goal_1 := 
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH11 : (list_within_bound UINT_MOD l_r_2 )) (PreH12 : ((Zlength (l_r_2)) = i)) (PreH13 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH14 : ((Zlength (l_a)) = n_pre)) (PreH15 : ((Zlength (l_b)) = n_pre)) (PreH16 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH17 : (list_within_bound UINT_MOD l_a )) (PreH18 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH19 : (list_within_bound UINT_MOD l_b )) (PreH20 : (n_pre >= 0)) ,
  (((list_to_Z (UINT_MOD) ((app (l_r_2) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((@nil Z))))))) + ((0 + 1 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) + (list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) ))
.

Definition mpn_add_n_entail_wit_2_2_split_goal_2 := 
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH11 : (list_within_bound UINT_MOD l_r_2 )) (PreH12 : ((Zlength (l_r_2)) = i)) (PreH13 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH14 : ((Zlength (l_a)) = n_pre)) (PreH15 : ((Zlength (l_b)) = n_pre)) (PreH16 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH17 : (list_within_bound UINT_MOD l_a )) (PreH18 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH19 : (list_within_bound UINT_MOD l_b )) (PreH20 : (n_pre >= 0)) ,
  ((Zlength ((app (l_r_2) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((@nil Z))))))) = (i + 1 ))
.

Definition mpn_add_n_entail_wit_2_2_split_goal_3 := 
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH11 : (list_within_bound UINT_MOD l_r_2 )) (PreH12 : ((Zlength (l_r_2)) = i)) (PreH13 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH14 : ((Zlength (l_a)) = n_pre)) (PreH15 : ((Zlength (l_b)) = n_pre)) (PreH16 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH17 : (list_within_bound UINT_MOD l_a )) (PreH18 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH19 : (list_within_bound UINT_MOD l_b )) (PreH20 : (n_pre >= 0)) ,
  (list_within_bound UINT_MOD (app (l_r_2) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((@nil Z))))) )
.

Definition mpn_add_n_entail_wit_2_3 := 
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH11 : (list_within_bound UINT_MOD l_r_2 )) (PreH12 : ((Zlength (l_r_2)) = i)) (PreH13 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH14 : ((Zlength (l_a)) = n_pre)) (PreH15 : ((Zlength (l_b)) = n_pre)) (PreH16 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH17 : (list_within_bound UINT_MOD l_a )) (PreH18 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH19 : (list_within_bound UINT_MOD l_b )) (PreH20 : (n_pre >= 0)) ,
  (UIntArray.full rp_pre (i + 1 ) (app (l_r_2) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
|--
  EX (val_r: Z)  (l_r: (@list Z))  (val_b_prefix: Z)  (val_a_prefix: Z) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (1 + 0 )) ” 
  &&  “ ((1 + 0 ) <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((Zlength (l_r)) = (i + 1 )) ” 
  &&  “ ((val_r + ((1 + 0 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.full rp_pre (i + 1 ) l_r )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
) \/
(
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH11 : (list_within_bound UINT_MOD l_r_2 )) (PreH12 : ((Zlength (l_r_2)) = i)) (PreH13 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH14 : ((Zlength (l_a)) = n_pre)) (PreH15 : ((Zlength (l_b)) = n_pre)) (PreH16 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH17 : (list_within_bound UINT_MOD l_a )) (PreH18 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH19 : (list_within_bound UINT_MOD l_b )) (PreH20 : (n_pre >= 0)) ,
  TT && emp 
|--
  “ (((list_to_Z (UINT_MOD) ((app (l_r_2) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((@nil Z))))))) + ((1 + 0 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) + (list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) )) ” 
  &&  “ ((Zlength ((app (l_r_2) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((@nil Z))))))) = (i + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD (app (l_r_2) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((@nil Z))))) ) ”
  &&  emp
).

Definition mpn_add_n_entail_wit_2_3_split_goal_1 := 
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH11 : (list_within_bound UINT_MOD l_r_2 )) (PreH12 : ((Zlength (l_r_2)) = i)) (PreH13 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH14 : ((Zlength (l_a)) = n_pre)) (PreH15 : ((Zlength (l_b)) = n_pre)) (PreH16 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH17 : (list_within_bound UINT_MOD l_a )) (PreH18 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH19 : (list_within_bound UINT_MOD l_b )) (PreH20 : (n_pre >= 0)) ,
  (((list_to_Z (UINT_MOD) ((app (l_r_2) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((@nil Z))))))) + ((1 + 0 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) + (list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) ))
.

Definition mpn_add_n_entail_wit_2_3_split_goal_2 := 
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH11 : (list_within_bound UINT_MOD l_r_2 )) (PreH12 : ((Zlength (l_r_2)) = i)) (PreH13 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH14 : ((Zlength (l_a)) = n_pre)) (PreH15 : ((Zlength (l_b)) = n_pre)) (PreH16 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH17 : (list_within_bound UINT_MOD l_a )) (PreH18 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH19 : (list_within_bound UINT_MOD l_b )) (PreH20 : (n_pre >= 0)) ,
  ((Zlength ((app (l_r_2) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((@nil Z))))))) = (i + 1 ))
.

Definition mpn_add_n_entail_wit_2_3_split_goal_3 := 
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH11 : (list_within_bound UINT_MOD l_r_2 )) (PreH12 : ((Zlength (l_r_2)) = i)) (PreH13 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH14 : ((Zlength (l_a)) = n_pre)) (PreH15 : ((Zlength (l_b)) = n_pre)) (PreH16 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH17 : (list_within_bound UINT_MOD l_a )) (PreH18 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH19 : (list_within_bound UINT_MOD l_b )) (PreH20 : (n_pre >= 0)) ,
  (list_within_bound UINT_MOD (app (l_r_2) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((@nil Z))))) )
.

Definition mpn_add_n_entail_wit_2_4 := 
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH11 : (list_within_bound UINT_MOD l_r_2 )) (PreH12 : ((Zlength (l_r_2)) = i)) (PreH13 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH14 : ((Zlength (l_a)) = n_pre)) (PreH15 : ((Zlength (l_b)) = n_pre)) (PreH16 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH17 : (list_within_bound UINT_MOD l_a )) (PreH18 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH19 : (list_within_bound UINT_MOD l_b )) (PreH20 : (n_pre >= 0)) ,
  (UIntArray.full rp_pre (i + 1 ) (app (l_r_2) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
|--
  EX (val_r: Z)  (l_r: (@list Z))  (val_b_prefix: Z)  (val_a_prefix: Z) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (1 + 1 )) ” 
  &&  “ ((1 + 1 ) <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((Zlength (l_r)) = (i + 1 )) ” 
  &&  “ ((val_r + ((1 + 1 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.full rp_pre (i + 1 ) l_r )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
) \/
(
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH11 : (list_within_bound UINT_MOD l_r_2 )) (PreH12 : ((Zlength (l_r_2)) = i)) (PreH13 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH14 : ((Zlength (l_a)) = n_pre)) (PreH15 : ((Zlength (l_b)) = n_pre)) (PreH16 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH17 : (list_within_bound UINT_MOD l_a )) (PreH18 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH19 : (list_within_bound UINT_MOD l_b )) (PreH20 : (n_pre >= 0)) ,
  TT && emp 
|--
  “ (((list_to_Z (UINT_MOD) ((app (l_r_2) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((@nil Z))))))) + ((1 + 1 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) + (list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) )) ” 
  &&  “ ((Zlength ((app (l_r_2) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((@nil Z))))))) = (i + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD (app (l_r_2) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((@nil Z))))) ) ”
  &&  emp
).

Definition mpn_add_n_entail_wit_2_4_split_goal_1 := 
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH11 : (list_within_bound UINT_MOD l_r_2 )) (PreH12 : ((Zlength (l_r_2)) = i)) (PreH13 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH14 : ((Zlength (l_a)) = n_pre)) (PreH15 : ((Zlength (l_b)) = n_pre)) (PreH16 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH17 : (list_within_bound UINT_MOD l_a )) (PreH18 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH19 : (list_within_bound UINT_MOD l_b )) (PreH20 : (n_pre >= 0)) ,
  (((list_to_Z (UINT_MOD) ((app (l_r_2) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((@nil Z))))))) + ((1 + 1 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) + (list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) ))
.

Definition mpn_add_n_entail_wit_2_4_split_goal_2 := 
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH11 : (list_within_bound UINT_MOD l_r_2 )) (PreH12 : ((Zlength (l_r_2)) = i)) (PreH13 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH14 : ((Zlength (l_a)) = n_pre)) (PreH15 : ((Zlength (l_b)) = n_pre)) (PreH16 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH17 : (list_within_bound UINT_MOD l_a )) (PreH18 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH19 : (list_within_bound UINT_MOD l_b )) (PreH20 : (n_pre >= 0)) ,
  ((Zlength ((app (l_r_2) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((@nil Z))))))) = (i + 1 ))
.

Definition mpn_add_n_entail_wit_2_4_split_goal_3 := 
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH11 : (list_within_bound UINT_MOD l_r_2 )) (PreH12 : ((Zlength (l_r_2)) = i)) (PreH13 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH14 : ((Zlength (l_a)) = n_pre)) (PreH15 : ((Zlength (l_b)) = n_pre)) (PreH16 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH17 : (list_within_bound UINT_MOD l_a )) (PreH18 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH19 : (list_within_bound UINT_MOD l_b )) (PreH20 : (n_pre >= 0)) ,
  (list_within_bound UINT_MOD (app (l_r_2) ((cons ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((@nil Z))))) )
.

Definition mpn_add_n_return_wit_1 := 
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= cy)) (PreH5 : (cy <= UINT_MAX)) (PreH6 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH7 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH8 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH9 : (list_within_bound UINT_MOD l_r )) (PreH10 : ((Zlength (l_r)) = i)) (PreH11 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH12 : ((Zlength (l_a)) = n_pre)) (PreH13 : ((Zlength (l_b)) = n_pre)) (PreH14 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH15 : (list_within_bound UINT_MOD l_a )) (PreH16 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH17 : (list_within_bound UINT_MOD l_b )) (PreH18 : (n_pre >= 0)) ,
  (UIntArray.full rp_pre i l_r )
  **  (UIntArray.undef_seg rp_pre i n_pre )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
|--
  EX (val_r_out: Z) ,
  “ ((val_r_out + (cy * (Z.pow (UINT_MOD) (n_pre)) ) ) = (val_a + val_b )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a n_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b n_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_out n_pre )
) \/
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= cy)) (PreH5 : (cy <= UINT_MAX)) (PreH6 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH7 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH8 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH9 : (list_within_bound UINT_MOD l_r )) (PreH10 : ((Zlength (l_r)) = i)) (PreH11 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH12 : ((Zlength (l_a)) = n_pre)) (PreH13 : ((Zlength (l_b)) = n_pre)) (PreH14 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH15 : (list_within_bound UINT_MOD l_a )) (PreH16 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH17 : (list_within_bound UINT_MOD l_b )) (PreH18 : (n_pre >= 0)) ,
  (UIntArray.full rp_pre i l_r )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
|--
  EX (val_r_out: Z) ,
  “ ((val_r_out + (cy * (Z.pow (UINT_MOD) (n_pre)) ) ) = (val_a + val_b )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a n_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b n_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_out n_pre )
).

Definition mpn_add_n_partial_solve_wit_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (PreH1 : (n_pre >= 0)) ,
  (mpd_store_Z UINT_MOD ap_pre val_a n_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b n_pre )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (n_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a n_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b n_pre )
  **  (UIntArray.undef_full rp_pre n_pre )
.

Definition mpn_add_n_partial_solve_wit_2 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= cy)) (PreH5 : (cy <= UINT_MAX)) (PreH6 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH7 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH8 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH9 : (list_within_bound UINT_MOD l_r )) (PreH10 : ((Zlength (l_r)) = i)) (PreH11 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH12 : ((Zlength (l_a)) = n_pre)) (PreH13 : ((Zlength (l_b)) = n_pre)) (PreH14 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH15 : (list_within_bound UINT_MOD l_a )) (PreH16 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH17 : (list_within_bound UINT_MOD l_b )) (PreH18 : (n_pre >= 0)) ,
  (UIntArray.full rp_pre i l_r )
  **  (UIntArray.undef_seg rp_pre i n_pre )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (((ap_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth i l_a 0))
  **  (UIntArray.missing_i ap_pre i 0 n_pre l_a )
  **  (UIntArray.full rp_pre i l_r )
  **  (UIntArray.undef_seg rp_pre i n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
.

Definition mpn_add_n_partial_solve_wit_3 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= cy)) (PreH5 : (cy <= UINT_MAX)) (PreH6 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH7 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH8 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH9 : (list_within_bound UINT_MOD l_r )) (PreH10 : ((Zlength (l_r)) = i)) (PreH11 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH12 : ((Zlength (l_a)) = n_pre)) (PreH13 : ((Zlength (l_b)) = n_pre)) (PreH14 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH15 : (list_within_bound UINT_MOD l_a )) (PreH16 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH17 : (list_within_bound UINT_MOD l_b )) (PreH18 : (n_pre >= 0)) ,
  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full rp_pre i l_r )
  **  (UIntArray.undef_seg rp_pre i n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (((bp_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth i l_b 0))
  **  (UIntArray.missing_i bp_pre i 0 n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full rp_pre i l_r )
  **  (UIntArray.undef_seg rp_pre i n_pre )
.

Definition mpn_add_n_partial_solve_wit_4 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH11 : (list_within_bound UINT_MOD l_r )) (PreH12 : ((Zlength (l_r)) = i)) (PreH13 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH14 : ((Zlength (l_a)) = n_pre)) (PreH15 : ((Zlength (l_b)) = n_pre)) (PreH16 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH17 : (list_within_bound UINT_MOD l_a )) (PreH18 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH19 : (list_within_bound UINT_MOD l_b )) (PreH20 : (n_pre >= 0)) ,
  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full rp_pre i l_r )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full rp_pre i l_r )
.

Definition mpn_add_n_partial_solve_wit_5 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH11 : (list_within_bound UINT_MOD l_r )) (PreH12 : ((Zlength (l_r)) = i)) (PreH13 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH14 : ((Zlength (l_a)) = n_pre)) (PreH15 : ((Zlength (l_b)) = n_pre)) (PreH16 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH17 : (list_within_bound UINT_MOD l_a )) (PreH18 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH19 : (list_within_bound UINT_MOD l_b )) (PreH20 : (n_pre >= 0)) ,
  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full rp_pre i l_r )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full rp_pre i l_r )
.

Definition mpn_add_n_partial_solve_wit_6 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH11 : (list_within_bound UINT_MOD l_r )) (PreH12 : ((Zlength (l_r)) = i)) (PreH13 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH14 : ((Zlength (l_a)) = n_pre)) (PreH15 : ((Zlength (l_b)) = n_pre)) (PreH16 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH17 : (list_within_bound UINT_MOD l_a )) (PreH18 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH19 : (list_within_bound UINT_MOD l_b )) (PreH20 : (n_pre >= 0)) ,
  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full rp_pre i l_r )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full rp_pre i l_r )
.

Definition mpn_add_n_partial_solve_wit_7 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= UINT_MAX)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH11 : (list_within_bound UINT_MOD l_r )) (PreH12 : ((Zlength (l_r)) = i)) (PreH13 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH14 : ((Zlength (l_a)) = n_pre)) (PreH15 : ((Zlength (l_b)) = n_pre)) (PreH16 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH17 : (list_within_bound UINT_MOD l_a )) (PreH18 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH19 : (list_within_bound UINT_MOD l_b )) (PreH20 : (n_pre >= 0)) ,
  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full rp_pre i l_r )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= UINT_MAX) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (n_pre >= 0) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full rp_pre i l_r )
.

Definition mpn_add_n_which_implies_wit_1 := 
(
forall (val_b: Z) (val_a: Z) (n: Z) (ap: Z) (bp: Z) ,
  (mpd_store_Z UINT_MOD ap val_a n )
  **  (mpd_store_Z UINT_MOD bp val_b n )
|--
  EX (l_b: (@list Z))  (l_a: (@list Z)) ,
  “ ((Zlength (l_a)) = n) ” 
  &&  “ ((Zlength (l_b)) = n) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ”
  &&  (UIntArray.full ap n l_a )
  **  (UIntArray.full bp n l_b )
) \/
(
forall (val_b: Z) (val_a: Z) (n: Z) (ap: Z) (bp: Z) ,
  (mpd_store_Z UINT_MOD ap val_a n )
  **  (mpd_store_Z UINT_MOD bp val_b n )
|--
  EX (l_b: (@list Z))  (l_a: (@list Z)) ,
  “ ((Zlength (l_a)) = n) ” 
  &&  “ ((Zlength (l_b)) = n) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ”
  &&  (UIntArray.full ap n l_a )
  **  (UIntArray.full bp n l_b )
).

(*----- Function mpn_add -----*)

Definition mpn_add_safety_wit_1 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_low: Z) (val_a_high: Z) (val_r_out: Z) (retval: Z) (l_r: (@list Z)) (PreH1 : (an_pre > bn_pre)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= UINT_MAX)) (PreH4 : (an_pre <= INT_MAX)) (PreH5 : (bn_pre <= INT_MAX)) (PreH6 : (an_pre >= INT_MIN)) (PreH7 : (bn_pre >= INT_MIN)) (PreH8 : ((Zlength (l_r)) = bn_pre)) (PreH9 : ((list_to_Z (UINT_MOD) (l_r)) = val_r_out)) (PreH10 : (list_within_bound UINT_MOD l_r )) (PreH11 : ((val_r_out + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b ))) (PreH12 : (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH13 : (an_pre >= bn_pre)) (PreH14 : (an_pre >= 0)) (PreH15 : (bn_pre >= 0)) ,
  ((( &( "cy" ) )) # UInt  |-> retval)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
|--
  “ ((an_pre - bn_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (an_pre - bn_pre )) ”
.

Definition mpn_add_entail_wit_1 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_low: Z) (val_a_high: Z) (val_r_out: Z) (retval: Z) (l_r: (@list Z)) (PreH1 : ((Zlength (l_r)) = bn_pre)) (PreH2 : ((list_to_Z (UINT_MOD) (l_r)) = val_r_out)) (PreH3 : (list_within_bound UINT_MOD l_r )) (PreH4 : ((val_r_out + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b ))) (PreH5 : (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH6 : (an_pre >= bn_pre)) (PreH7 : (an_pre >= 0)) (PreH8 : (bn_pre >= 0)) ,
  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  ((( &( "cy" ) )) # UInt  |-> retval)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (an_pre <= INT_MAX) ” 
  &&  “ (bn_pre <= INT_MAX) ” 
  &&  “ (an_pre >= INT_MIN) ” 
  &&  “ (bn_pre >= INT_MIN) ” 
  &&  “ ((Zlength (l_r)) = bn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r_out) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((val_r_out + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b )) ” 
  &&  “ (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  ((( &( "cy" ) )) # UInt  |-> retval)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
.

Definition mpn_add_return_wit_1 := 
(
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_low: Z) (val_a_high: Z) (val_r_out_2: Z) (retval_2: Z) (l_r: (@list Z)) (val': Z) (retval: Z) (PreH1 : ((val' + (retval * (Z.pow (UINT_MOD) ((an_pre - bn_pre ))) ) ) = (val_a_high + retval_2 ))) (PreH2 : (an_pre > bn_pre)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= UINT_MAX)) (PreH5 : (an_pre <= INT_MAX)) (PreH6 : (bn_pre <= INT_MAX)) (PreH7 : (an_pre >= INT_MIN)) (PreH8 : (bn_pre >= INT_MIN)) (PreH9 : ((Zlength (l_r)) = bn_pre)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r)) = val_r_out_2)) (PreH11 : (list_within_bound UINT_MOD l_r )) (PreH12 : ((val_r_out_2 + (retval_2 * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b ))) (PreH13 : (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH14 : (an_pre >= bn_pre)) (PreH15 : (an_pre >= 0)) (PreH16 : (bn_pre >= 0)) ,
  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (rp_pre + (bn_pre * sizeof(UINT))) val' (an_pre - bn_pre ) )
  **  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
|--
  EX (val_r_out: Z) ,
  “ ((val_r_out + (retval * (Z.pow (UINT_MOD) (an_pre)) ) ) = (val_a + val_b )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_out an_pre )
) \/
(
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_low: Z) (val_a_high: Z) (val_r_out_2: Z) (retval_2: Z) (l_r: (@list Z)) (val': Z) (retval: Z) (PreH1 : ((val' + (retval * (Z.pow (UINT_MOD) ((an_pre - bn_pre ))) ) ) = (val_a_high + retval_2 ))) (PreH2 : (an_pre > bn_pre)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= UINT_MAX)) (PreH5 : (an_pre <= INT_MAX)) (PreH6 : (bn_pre <= INT_MAX)) (PreH7 : (an_pre >= INT_MIN)) (PreH8 : (bn_pre >= INT_MIN)) (PreH9 : ((Zlength (l_r)) = bn_pre)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r)) = val_r_out_2)) (PreH11 : (list_within_bound UINT_MOD l_r )) (PreH12 : ((val_r_out_2 + (retval_2 * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b ))) (PreH13 : (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH14 : (an_pre >= bn_pre)) (PreH15 : (an_pre >= 0)) (PreH16 : (bn_pre >= 0)) ,
  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (rp_pre + (bn_pre * sizeof(UINT))) val' (an_pre - bn_pre ) )
  **  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
|--
  EX (val_r_out: Z) ,
  “ ((val_r_out + (retval * (Z.pow (UINT_MOD) (an_pre)) ) ) = (val_a + val_b )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_out an_pre )
).

Definition mpn_add_return_wit_2 := 
(
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_low: Z) (val_a_high: Z) (val_r_out_2: Z) (retval: Z) (l_r: (@list Z)) (PreH1 : (an_pre <= bn_pre)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= UINT_MAX)) (PreH4 : (an_pre <= INT_MAX)) (PreH5 : (bn_pre <= INT_MAX)) (PreH6 : (an_pre >= INT_MIN)) (PreH7 : (bn_pre >= INT_MIN)) (PreH8 : ((Zlength (l_r)) = bn_pre)) (PreH9 : ((list_to_Z (UINT_MOD) (l_r)) = val_r_out_2)) (PreH10 : (list_within_bound UINT_MOD l_r )) (PreH11 : ((val_r_out_2 + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b ))) (PreH12 : (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH13 : (an_pre >= bn_pre)) (PreH14 : (an_pre >= 0)) (PreH15 : (bn_pre >= 0)) ,
  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
|--
  EX (val_r_out: Z) ,
  “ ((val_r_out + (retval * (Z.pow (UINT_MOD) (an_pre)) ) ) = (val_a + val_b )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_out an_pre )
) \/
(
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_low: Z) (val_a_high: Z) (val_r_out_2: Z) (retval: Z) (l_r: (@list Z)) (PreH1 : (an_pre <= bn_pre)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= UINT_MAX)) (PreH4 : (an_pre <= INT_MAX)) (PreH5 : (bn_pre <= INT_MAX)) (PreH6 : (an_pre >= INT_MIN)) (PreH7 : (bn_pre >= INT_MIN)) (PreH8 : ((Zlength (l_r)) = bn_pre)) (PreH9 : ((list_to_Z (UINT_MOD) (l_r)) = val_r_out_2)) (PreH10 : (list_within_bound UINT_MOD l_r )) (PreH11 : ((val_r_out_2 + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b ))) (PreH12 : (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH13 : (an_pre >= bn_pre)) (PreH14 : (an_pre >= 0)) (PreH15 : (bn_pre >= 0)) ,
  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
|--
  EX (val_r_out: Z) ,
  “ ((val_r_out + (retval * (Z.pow (UINT_MOD) (an_pre)) ) ) = (val_a + val_b )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_out an_pre )
).

Definition mpn_add_partial_solve_wit_1_pure := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (PreH1 : (an_pre >= bn_pre)) (PreH2 : (an_pre >= 0)) (PreH3 : (bn_pre >= 0)) ,
  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (mpd_store_Z UINT_MOD ap_pre val_a an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full rp_pre an_pre )
|--
  “ (an_pre >= bn_pre) ” 
  &&  “ (bn_pre >= 0) ”
.

Definition mpn_add_partial_solve_wit_1_aux := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (PreH1 : (an_pre >= bn_pre)) (PreH2 : (an_pre >= 0)) (PreH3 : (bn_pre >= 0)) ,
  (mpd_store_Z UINT_MOD ap_pre val_a an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full rp_pre an_pre )
|--
  “ (an_pre >= bn_pre) ” 
  &&  “ (bn_pre >= 0) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full rp_pre an_pre )
.

Definition mpn_add_partial_solve_wit_1 := mpn_add_partial_solve_wit_1_pure -> mpn_add_partial_solve_wit_1_aux.

Definition mpn_add_partial_solve_wit_2_pure := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_low: Z) (val_a_high: Z) (PreH1 : (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH2 : (an_pre >= bn_pre)) (PreH3 : (an_pre >= 0)) (PreH4 : (bn_pre >= 0)) ,
  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full rp_pre an_pre )
|--
  “ (an_pre >= bn_pre) ” 
  &&  “ (bn_pre >= 0) ”
.

Definition mpn_add_partial_solve_wit_2_aux := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_low: Z) (val_a_high: Z) (PreH1 : (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH2 : (an_pre >= bn_pre)) (PreH3 : (an_pre >= 0)) (PreH4 : (bn_pre >= 0)) ,
  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full rp_pre an_pre )
|--
  “ (an_pre >= bn_pre) ” 
  &&  “ (bn_pre >= 0) ” 
  &&  “ (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (UIntArray.undef_full rp_pre an_pre )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
.

Definition mpn_add_partial_solve_wit_2 := mpn_add_partial_solve_wit_2_pure -> mpn_add_partial_solve_wit_2_aux.

Definition mpn_add_partial_solve_wit_3_pure := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_low: Z) (val_a_high: Z) (PreH1 : (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH2 : (an_pre >= bn_pre)) (PreH3 : (an_pre >= 0)) (PreH4 : (bn_pre >= 0)) ,
  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.undef_full rp_pre bn_pre )
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
|--
  “ (bn_pre >= 0) ”
.

Definition mpn_add_partial_solve_wit_3_aux := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_low: Z) (val_a_high: Z) (PreH1 : (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH2 : (an_pre >= bn_pre)) (PreH3 : (an_pre >= 0)) (PreH4 : (bn_pre >= 0)) ,
  (UIntArray.undef_full rp_pre bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
|--
  “ (bn_pre >= 0) ” 
  &&  “ (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full rp_pre bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
.

Definition mpn_add_partial_solve_wit_3 := mpn_add_partial_solve_wit_3_pure -> mpn_add_partial_solve_wit_3_aux.

Definition mpn_add_partial_solve_wit_4 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_low: Z) (val_a_high: Z) (val_r_out: Z) (retval: Z) (PreH1 : ((val_r_out + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b ))) (PreH2 : (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH3 : (an_pre >= bn_pre)) (PreH4 : (an_pre >= 0)) (PreH5 : (bn_pre >= 0)) ,
  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_out bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
|--
  “ ((val_r_out + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b )) ” 
  &&  “ (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD rp_pre val_r_out bn_pre )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
.

Definition mpn_add_partial_solve_wit_5_pure := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_low: Z) (val_a_high: Z) (val_r_out: Z) (retval: Z) (l_r: (@list Z)) (PreH1 : (an_pre > bn_pre)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= UINT_MAX)) (PreH4 : (an_pre <= INT_MAX)) (PreH5 : (bn_pre <= INT_MAX)) (PreH6 : (an_pre >= INT_MIN)) (PreH7 : (bn_pre >= INT_MIN)) (PreH8 : ((Zlength (l_r)) = bn_pre)) (PreH9 : ((list_to_Z (UINT_MOD) (l_r)) = val_r_out)) (PreH10 : (list_within_bound UINT_MOD l_r )) (PreH11 : ((val_r_out + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b ))) (PreH12 : (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH13 : (an_pre >= bn_pre)) (PreH14 : (an_pre >= 0)) (PreH15 : (bn_pre >= 0)) ,
  ((( &( "cy" ) )) # UInt  |-> retval)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
|--
  “ ((an_pre - bn_pre ) > 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ”
.

Definition mpn_add_partial_solve_wit_5_aux := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_low: Z) (val_a_high: Z) (val_r_out: Z) (retval: Z) (l_r: (@list Z)) (PreH1 : (an_pre > bn_pre)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= UINT_MAX)) (PreH4 : (an_pre <= INT_MAX)) (PreH5 : (bn_pre <= INT_MAX)) (PreH6 : (an_pre >= INT_MIN)) (PreH7 : (bn_pre >= INT_MIN)) (PreH8 : ((Zlength (l_r)) = bn_pre)) (PreH9 : ((list_to_Z (UINT_MOD) (l_r)) = val_r_out)) (PreH10 : (list_within_bound UINT_MOD l_r )) (PreH11 : ((val_r_out + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b ))) (PreH12 : (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH13 : (an_pre >= bn_pre)) (PreH14 : (an_pre >= 0)) (PreH15 : (bn_pre >= 0)) ,
  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
|--
  “ ((an_pre - bn_pre ) > 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (an_pre > bn_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (an_pre <= INT_MAX) ” 
  &&  “ (bn_pre <= INT_MAX) ” 
  &&  “ (an_pre >= INT_MIN) ” 
  &&  “ (bn_pre >= INT_MIN) ” 
  &&  “ ((Zlength (l_r)) = bn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r_out) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((val_r_out + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b )) ” 
  &&  “ (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre >= 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_high (an_pre - bn_pre ) )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
  **  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
.

Definition mpn_add_partial_solve_wit_5 := mpn_add_partial_solve_wit_5_pure -> mpn_add_partial_solve_wit_5_aux.

Definition mpn_add_which_implies_wit_1 := 
(
forall (val_a: Z) (an: Z) (ap: Z) (bn: Z) (PreH1 : (an >= bn)) (PreH2 : (bn >= 0)) ,
  (mpd_store_Z UINT_MOD ap val_a an )
|--
  EX (val_a_high: Z)  (val_a_low: Z) ,
  “ (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn)) ) )) ”
  &&  (mpd_store_Z UINT_MOD ap val_a_low bn )
  **  (mpd_store_Z UINT_MOD (ap + (bn * sizeof(UINT))) val_a_high (an - bn ) )
) \/
(
forall (val_a: Z) (an: Z) (ap: Z) (bn: Z) (PreH1 : (an >= bn)) (PreH2 : (bn >= 0)) ,
  (mpd_store_Z UINT_MOD ap val_a an )
|--
  EX (val_a_high: Z)  (val_a_low: Z) ,
  “ (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn)) ) )) ”
  &&  (mpd_store_Z UINT_MOD ap val_a_low bn )
  **  (mpd_store_Z UINT_MOD (ap + (bn * sizeof(UINT))) val_a_high (an - bn ) )
).

Definition mpn_add_which_implies_wit_2 := 
(
forall (an: Z) (bn: Z) (rp: Z) (PreH1 : (an >= bn)) (PreH2 : (bn >= 0)) ,
  (UIntArray.undef_full rp an )
|--
  (UIntArray.undef_full rp bn )
  **  (UIntArray.undef_full (rp + (bn * sizeof(UINT))) (an - bn ) )
) \/
(
forall (an: Z) (bn: Z) (rp: Z) (PreH1 : (an >= bn)) (PreH2 : (bn >= 0)) ,
  (UIntArray.undef_full rp an )
|--
  (UIntArray.undef_full rp bn )
  **  (UIntArray.undef_full (rp + (bn * sizeof(UINT))) (an - bn ) )
).

Definition mpn_add_which_implies_wit_2_split_goal_spatial := 
forall (an: Z) (bn: Z) (rp: Z) (PreH1 : (an >= bn)) (PreH2 : (bn >= 0)) ,
  (UIntArray.undef_full rp an )
|--
  (UIntArray.undef_full rp bn )
  **  (UIntArray.undef_full (rp + (bn * sizeof(UINT))) (an - bn ) )
.

Definition mpn_add_which_implies_wit_3 := 
(
forall (val_r_out: Z) (bn: Z) (rp: Z) ,
  (mpd_store_Z UINT_MOD rp val_r_out bn )
|--
  EX (l_r: (@list Z)) ,
  “ ((Zlength (l_r)) = bn) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r_out) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ”
  &&  (UIntArray.full rp bn l_r )
) \/
(
forall (val_r_out: Z) (bn: Z) (rp: Z) ,
  (mpd_store_Z UINT_MOD rp val_r_out bn )
|--
  EX (l_r: (@list Z)) ,
  “ ((Zlength (l_r)) = bn) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r_out) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ”
  &&  (UIntArray.full rp bn l_r )
).

(*----- Function gmp_umul_ppmm -----*)

Definition gmp_umul_ppmm_safety_wit_1 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) (PreH1 : (0 <= v_pre)) (PreH2 : (v_pre <= UINT_MAX)) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre <= UINT_MAX)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (v_pre <= UINT_MAX)) (PreH7 : (u_pre >= 0)) (PreH8 : (v_pre >= 0)) ,
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
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (65535 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65535) ”
.

Definition gmp_umul_ppmm_safety_wit_2 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) (PreH1 : (0 <= v_pre)) (PreH2 : (v_pre <= UINT_MAX)) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre <= UINT_MAX)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (v_pre <= UINT_MAX)) (PreH7 : (u_pre >= 0)) (PreH8 : (v_pre >= 0)) ,
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
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (16 <= 31) ” 
  &&  “ (0 <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_3 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) (PreH1 : (0 <= v_pre)) (PreH2 : (v_pre <= UINT_MAX)) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre <= UINT_MAX)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (v_pre <= UINT_MAX)) (PreH7 : (u_pre >= 0)) (PreH8 : (v_pre >= 0)) ,
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
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (16 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_4 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) (PreH1 : (0 <= v_pre)) (PreH2 : (v_pre <= UINT_MAX)) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre <= UINT_MAX)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (v_pre <= UINT_MAX)) (PreH7 : (u_pre >= 0)) (PreH8 : (v_pre >= 0)) ,
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
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (65535 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65535) ”
.

Definition gmp_umul_ppmm_safety_wit_5 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) (PreH1 : (0 <= v_pre)) (PreH2 : (v_pre <= UINT_MAX)) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre <= UINT_MAX)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (v_pre <= UINT_MAX)) (PreH7 : (u_pre >= 0)) (PreH8 : (v_pre >= 0)) ,
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
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (16 <= 31) ” 
  &&  “ (0 <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_6 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) (PreH1 : (0 <= v_pre)) (PreH2 : (v_pre <= UINT_MAX)) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre <= UINT_MAX)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (v_pre <= UINT_MAX)) (PreH7 : (u_pre >= 0)) (PreH8 : (v_pre >= 0)) ,
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
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (16 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_7 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) (PreH1 : (0 <= v_pre)) (PreH2 : (v_pre <= UINT_MAX)) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre <= UINT_MAX)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (v_pre <= UINT_MAX)) (PreH7 : (u_pre >= 0)) (PreH8 : (v_pre >= 0)) ,
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
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (16 <= 31) ” 
  &&  “ (0 <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_8 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) (PreH1 : (0 <= v_pre)) (PreH2 : (v_pre <= UINT_MAX)) (PreH3 : (0 <= u_pre)) (PreH4 : (u_pre <= UINT_MAX)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (v_pre <= UINT_MAX)) (PreH7 : (u_pre >= 0)) (PreH8 : (v_pre >= 0)) ,
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
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (16 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_9 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) < (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= UINT_MAX)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (u_pre >= 0)) (PreH9 : (v_pre >= 0)) ,
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
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (65536 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65536) ”
.

Definition gmp_umul_ppmm_safety_wit_10 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) < (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= UINT_MAX)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (u_pre >= 0)) (PreH9 : (v_pre >= 0)) ,
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
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (16 <= 31) ” 
  &&  “ (0 <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_11 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) < (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= UINT_MAX)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (u_pre >= 0)) (PreH9 : (v_pre >= 0)) ,
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
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (16 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_12 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) >= (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= UINT_MAX)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (u_pre >= 0)) (PreH9 : (v_pre >= 0)) ,
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
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (16 <= 31) ” 
  &&  “ (0 <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_13 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) >= (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= UINT_MAX)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (u_pre >= 0)) (PreH9 : (v_pre >= 0)) ,
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
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
|--
  “ (16 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_14 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) < (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= UINT_MAX)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (u_pre >= 0)) (PreH9 : (v_pre >= 0)) ,
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
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + 65536 )) (32)) + (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16) )) (32)))
|--
  “ (16 <= 31) ” 
  &&  “ (0 <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_15 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) < (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= UINT_MAX)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (u_pre >= 0)) (PreH9 : (v_pre >= 0)) ,
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
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + 65536 )) (32)) + (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16) )) (32)))
|--
  “ (16 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_16 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) < (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= UINT_MAX)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (u_pre >= 0)) (PreH9 : (v_pre >= 0)) ,
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
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + 65536 )) (32)) + (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16) )) (32)))
|--
  “ (65535 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65535) ”
.

Definition gmp_umul_ppmm_safety_wit_17 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) >= (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= UINT_MAX)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (u_pre >= 0)) (PreH9 : (v_pre >= 0)) ,
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
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16) )) (32)))
|--
  “ (16 <= 31) ” 
  &&  “ (0 <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_18 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) >= (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= UINT_MAX)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (u_pre >= 0)) (PreH9 : (v_pre >= 0)) ,
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
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16) )) (32)))
|--
  “ (16 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 16) ”
.

Definition gmp_umul_ppmm_safety_wit_19 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) >= (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= UINT_MAX)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (u_pre >= 0)) (PreH9 : (v_pre >= 0)) ,
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
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16) )) (32)))
|--
  “ (65535 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65535) ”
.

Definition gmp_umul_ppmm_entail_wit_1 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) ,
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
  **  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "u" ) )) # UInt  |-> u_pre)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
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
  **  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
.

Definition gmp_umul_ppmm_entail_wit_2 := 
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) (PreH1 : (0 <= u_pre)) (PreH2 : (u_pre <= UINT_MAX)) (PreH3 : (u_pre <= UINT_MAX)) (PreH4 : (v_pre <= UINT_MAX)) (PreH5 : (u_pre >= 0)) (PreH6 : (v_pre >= 0)) ,
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
  **  ((( &( "v" ) )) # UInt  |-> v_pre)
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
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
  **  ((( &( "w1" ) )) # Ptr  |-> w1_pre)
  **  ((( &( "w0" ) )) # Ptr  |-> w0_pre)
  **  ((w0_pre) # UInt  |->_)
  **  ((w1_pre) # UInt  |->_)
.

Definition gmp_umul_ppmm_return_wit_1 := 
(
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) < (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= UINT_MAX)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (u_pre >= 0)) (PreH9 : (v_pre >= 0)) ,
  ((w0_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16)) (32)) + (Z.land ((Z.land u_pre 65535) * (Z.land v_pre 65535) ) 65535) )) (32)))
  **  ((w1_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + 65536 )) (32)) + (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16) )) (32)))
|--
  EX (w0_value: Z)  (w1_value: Z) ,
  “ (((w1_value * UINT_MOD ) + w0_value ) = (u_pre * v_pre )) ”
  &&  ((w0_pre) # UInt  |-> w0_value)
  **  ((w1_pre) # UInt  |-> w1_value)
) \/
(
forall (v_pre: Z) (u_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) < (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= UINT_MAX)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (u_pre >= 0)) (PreH9 : (v_pre >= 0)) ,
  TT && emp 
|--
  “ ((((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + 65536 )) (32)) + (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16) )) (32)) * UINT_MOD ) + (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16)) (32)) + (Z.land ((Z.land u_pre 65535) * (Z.land v_pre 65535) ) 65535) )) (32)) ) = (u_pre * v_pre )) ”
  &&  emp
).

Definition gmp_umul_ppmm_return_wit_1_split_goal_1 := 
forall (v_pre: Z) (u_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) < (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= UINT_MAX)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (u_pre >= 0)) (PreH9 : (v_pre >= 0)) ,
  ((((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + 65536 )) (32)) + (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16) )) (32)) * UINT_MOD ) + (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16)) (32)) + (Z.land ((Z.land u_pre 65535) * (Z.land v_pre 65535) ) 65535) )) (32)) ) = (u_pre * v_pre ))
.

Definition gmp_umul_ppmm_return_wit_2 := 
(
forall (v_pre: Z) (u_pre: Z) (w1_pre: Z) (w0_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) >= (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= UINT_MAX)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (u_pre >= 0)) (PreH9 : (v_pre >= 0)) ,
  ((w0_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16)) (32)) + (Z.land ((Z.land u_pre 65535) * (Z.land v_pre 65535) ) 65535) )) (32)))
  **  ((w1_pre) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16) )) (32)))
|--
  EX (w0_value: Z)  (w1_value: Z) ,
  “ (((w1_value * UINT_MOD ) + w0_value ) = (u_pre * v_pre )) ”
  &&  ((w0_pre) # UInt  |-> w0_value)
  **  ((w1_pre) # UInt  |-> w1_value)
) \/
(
forall (v_pre: Z) (u_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) >= (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= UINT_MAX)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (u_pre >= 0)) (PreH9 : (v_pre >= 0)) ,
  TT && emp 
|--
  “ ((((unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16) )) (32)) * UINT_MOD ) + (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16)) (32)) + (Z.land ((Z.land u_pre 65535) * (Z.land v_pre 65535) ) 65535) )) (32)) ) = (u_pre * v_pre )) ”
  &&  emp
).

Definition gmp_umul_ppmm_return_wit_2_split_goal_1 := 
forall (v_pre: Z) (u_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) >= (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)))) (PreH2 : (0 <= v_pre)) (PreH3 : (v_pre <= UINT_MAX)) (PreH4 : (0 <= u_pre)) (PreH5 : (u_pre <= UINT_MAX)) (PreH6 : (u_pre <= UINT_MAX)) (PreH7 : (v_pre <= UINT_MAX)) (PreH8 : (u_pre >= 0)) (PreH9 : (v_pre >= 0)) ,
  ((((unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16) )) (32)) * UINT_MOD ) + (unsigned_last_nbits (((unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits (((unsigned_last_nbits (((unsigned_last_nbits (((Z.land u_pre 65535) * (Z.shiftr v_pre 16) )) (32)) + (Z.shiftr (unsigned_last_nbits (((Z.land u_pre 65535) * (Z.land v_pre 65535) )) (32)) 16) )) (32)) + (unsigned_last_nbits (((Z.shiftr u_pre 16) * (Z.land v_pre 65535) )) (32)) )) (32)) 16)) (32)) + (Z.land ((Z.land u_pre 65535) * (Z.land v_pre 65535) ) 65535) )) (32)) ) = (u_pre * v_pre ))
.

(*----- Function mpn_mul_1 -----*)

Definition mpn_mul_1_safety_wit_1 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (list_within_bound UINT_MOD l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "lpl" ) )) # UInt  |->_)
  **  ((( &( "hpl" ) )) # UInt  |->_)
  **  ((( &( "cl" ) )) # UInt  |->_)
  **  ((( &( "ul" ) )) # UInt  |->_)
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_mul_1_safety_wit_2 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (list_within_bound UINT_MOD l )) ,
  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "lpl" ) )) # UInt  |->_)
  **  ((( &( "hpl" ) )) # UInt  |->_)
  **  ((( &( "cl" ) )) # UInt  |->_)
  **  ((( &( "ul" ) )) # UInt  |->_)
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_mul_1_safety_wit_3 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l: (@list Z)) (l_rp: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits ((lpl + cl )) (32)) >= cl)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= cl)) (PreH5 : (cl <= UINT_MAX)) (PreH6 : (0 <= lpl)) (PreH7 : (lpl <= UINT_MAX)) (PreH8 : (0 <= hpl)) (PreH9 : (hpl <= UINT_MAX)) (PreH10 : ((Zlength (l_rp)) = i)) (PreH11 : (list_within_bound UINT_MOD l_rp )) (PreH12 : (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))) (PreH13 : (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre ))) (PreH14 : (n_pre > 0)) (PreH15 : (n_pre <= INT_MAX)) (PreH16 : (0 <= vl_pre)) (PreH17 : (vl_pre <= UINT_MAX)) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (list_within_bound UINT_MOD l )) ,
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
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l: (@list Z)) (l_rp: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits ((lpl + cl )) (32)) >= cl)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= cl)) (PreH5 : (cl <= UINT_MAX)) (PreH6 : (0 <= lpl)) (PreH7 : (lpl <= UINT_MAX)) (PreH8 : (0 <= hpl)) (PreH9 : (hpl <= UINT_MAX)) (PreH10 : ((Zlength (l_rp)) = i)) (PreH11 : (list_within_bound UINT_MOD l_rp )) (PreH12 : (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))) (PreH13 : (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre ))) (PreH14 : (n_pre > 0)) (PreH15 : (n_pre <= INT_MAX)) (PreH16 : (0 <= vl_pre)) (PreH17 : (vl_pre <= UINT_MAX)) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (list_within_bound UINT_MOD l )) ,
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
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l: (@list Z)) (l_rp: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits ((lpl + cl )) (32)) < cl)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= cl)) (PreH5 : (cl <= UINT_MAX)) (PreH6 : (0 <= lpl)) (PreH7 : (lpl <= UINT_MAX)) (PreH8 : (0 <= hpl)) (PreH9 : (hpl <= UINT_MAX)) (PreH10 : ((Zlength (l_rp)) = i)) (PreH11 : (list_within_bound UINT_MOD l_rp )) (PreH12 : (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))) (PreH13 : (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre ))) (PreH14 : (n_pre > 0)) (PreH15 : (n_pre <= INT_MAX)) (PreH16 : (0 <= vl_pre)) (PreH17 : (vl_pre <= UINT_MAX)) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (list_within_bound UINT_MOD l )) ,
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
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l: (@list Z)) (l_rp: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits ((lpl + cl )) (32)) < cl)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= cl)) (PreH5 : (cl <= UINT_MAX)) (PreH6 : (0 <= lpl)) (PreH7 : (lpl <= UINT_MAX)) (PreH8 : (0 <= hpl)) (PreH9 : (hpl <= UINT_MAX)) (PreH10 : ((Zlength (l_rp)) = i)) (PreH11 : (list_within_bound UINT_MOD l_rp )) (PreH12 : (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))) (PreH13 : (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre ))) (PreH14 : (n_pre > 0)) (PreH15 : (n_pre <= INT_MAX)) (PreH16 : (0 <= vl_pre)) (PreH17 : (vl_pre <= UINT_MAX)) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (list_within_bound UINT_MOD l )) ,
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
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  EX (l_rp: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ ((Zlength (l_rp)) = 0) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + (0 * (Z.pow (UINT_MOD) (0)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (0) (l)))) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 0 l_rp )
  **  (UIntArray.undef_seg rp_pre 0 n_pre )
) \/
(
forall (vl_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (list_within_bound UINT_MOD l )) ,
  TT && emp 
|--
  “ (((list_to_Z (UINT_MOD) ((@nil Z))) + (0 * (Z.pow (UINT_MOD) (0)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (0) (l)))) * vl_pre )) ” 
  &&  “ (list_within_bound UINT_MOD (@nil Z) ) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ”
  &&  emp
).

Definition mpn_mul_1_entail_wit_1_split_goal_1 := 
forall (vl_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (list_within_bound UINT_MOD l )) ,
  (((list_to_Z (UINT_MOD) ((@nil Z))) + (0 * (Z.pow (UINT_MOD) (0)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (0) (l)))) * vl_pre ))
.

Definition mpn_mul_1_entail_wit_1_split_goal_2 := 
forall (vl_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (list_within_bound UINT_MOD l )) ,
  (list_within_bound UINT_MOD (@nil Z) )
.

Definition mpn_mul_1_entail_wit_1_split_goal_3 := 
forall (vl_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (list_within_bound UINT_MOD l )) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition mpn_mul_1_entail_wit_2 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l: (@list Z)) (l_rp: (@list Z)) (cl: Z) (i: Z) (w0_value: Z) (w1_value: Z) (PreH1 : (((w1_value * UINT_MOD ) + w0_value ) = ((Znth i l 0) * vl_pre ))) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= cl)) (PreH6 : (cl <= UINT_MAX)) (PreH7 : ((Zlength (l_rp)) = i)) (PreH8 : (list_within_bound UINT_MOD l_rp )) (PreH9 : (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))) (PreH10 : (n_pre > 0)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (0 <= vl_pre)) (PreH13 : (vl_pre <= UINT_MAX)) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (list_within_bound UINT_MOD l )) ,
  ((( &( "lpl" ) )) # UInt  |-> w0_value)
  **  ((( &( "hpl" ) )) # UInt  |-> w1_value)
  **  (UIntArray.full up_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # UInt  |-> cl)
  **  (UIntArray.seg rp_pre 0 i l_rp )
  **  (UIntArray.undef_seg rp_pre i n_pre )
  **  ((( &( "ul" ) )) # UInt  |-> (Znth i l 0))
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  “ (0 <= w0_value) ” 
  &&  “ (w0_value <= UINT_MAX) ” 
  &&  “ ((Znth i l 0) <= UINT_MAX) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (vl_pre >= 0) ” 
  &&  “ ((Znth i l 0) >= 0) ” 
  &&  “ (cl >= 0) ” 
  &&  “ (w1_value >= 0) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (((w1_value * UINT_MOD ) + w0_value ) = ((Znth i l 0) * vl_pre )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_rp)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  ((( &( "lpl" ) )) # UInt  |-> w0_value)
  **  ((( &( "hpl" ) )) # UInt  |-> w1_value)
  **  (UIntArray.full up_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # UInt  |-> cl)
  **  (UIntArray.seg rp_pre 0 i l_rp )
  **  (UIntArray.undef_seg rp_pre i n_pre )
  **  ((( &( "ul" ) )) # UInt  |-> (Znth i l 0))
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
.

Definition mpn_mul_1_entail_wit_3 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l: (@list Z)) (l_rp: (@list Z)) (cl: Z) (i: Z) (w0_value: Z) (w1_value: Z) (PreH1 : (0 <= w0_value)) (PreH2 : (w0_value <= UINT_MAX)) (PreH3 : ((Znth i l 0) <= UINT_MAX)) (PreH4 : (w1_value <= UINT_MAX)) (PreH5 : (vl_pre >= 0)) (PreH6 : ((Znth i l 0) >= 0)) (PreH7 : (cl >= 0)) (PreH8 : (w1_value >= 0)) (PreH9 : (i <= INT_MAX)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (((w1_value * UINT_MOD ) + w0_value ) = ((Znth i l 0) * vl_pre ))) (PreH13 : (i < n_pre)) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= cl)) (PreH17 : (cl <= UINT_MAX)) (PreH18 : ((Zlength (l_rp)) = i)) (PreH19 : (list_within_bound UINT_MOD l_rp )) (PreH20 : (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))) (PreH21 : (n_pre > 0)) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (0 <= vl_pre)) (PreH24 : (vl_pre <= UINT_MAX)) (PreH25 : ((Zlength (l)) = n_pre)) (PreH26 : (list_within_bound UINT_MOD l )) ,
  ((( &( "lpl" ) )) # UInt  |-> w0_value)
  **  ((( &( "hpl" ) )) # UInt  |-> w1_value)
  **  (UIntArray.full up_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # UInt  |-> cl)
  **  (UIntArray.seg rp_pre 0 i l_rp )
  **  (UIntArray.undef_seg rp_pre i n_pre )
  **  ((( &( "ul" ) )) # UInt  |-> (Znth i l 0))
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  “ (0 <= w1_value) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (w0_value >= 0) ” 
  &&  “ (0 <= w0_value) ” 
  &&  “ (w0_value <= UINT_MAX) ” 
  &&  “ ((Znth i l 0) <= UINT_MAX) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (vl_pre >= 0) ” 
  &&  “ ((Znth i l 0) >= 0) ” 
  &&  “ (cl >= 0) ” 
  &&  “ (w1_value >= 0) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (((w1_value * UINT_MOD ) + w0_value ) = ((Znth i l 0) * vl_pre )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_rp)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  ((( &( "hpl" ) )) # UInt  |-> w1_value)
  **  ((( &( "lpl" ) )) # UInt  |-> w0_value)
  **  (UIntArray.full up_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # UInt  |-> cl)
  **  (UIntArray.seg rp_pre 0 i l_rp )
  **  (UIntArray.undef_seg rp_pre i n_pre )
  **  ((( &( "ul" ) )) # UInt  |-> (Znth i l 0))
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
.

Definition mpn_mul_1_entail_wit_4 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l: (@list Z)) (l_rp_2: (@list Z)) (cl: Z) (i: Z) (w0_value: Z) (w1_value: Z) (PreH1 : (0 <= w1_value)) (PreH2 : (w1_value <= UINT_MAX)) (PreH3 : (w0_value >= 0)) (PreH4 : (0 <= w0_value)) (PreH5 : (w0_value <= UINT_MAX)) (PreH6 : ((Znth i l 0) <= UINT_MAX)) (PreH7 : (w1_value <= UINT_MAX)) (PreH8 : (vl_pre >= 0)) (PreH9 : ((Znth i l 0) >= 0)) (PreH10 : (cl >= 0)) (PreH11 : (w1_value >= 0)) (PreH12 : (i <= INT_MAX)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (((w1_value * UINT_MOD ) + w0_value ) = ((Znth i l 0) * vl_pre ))) (PreH16 : (i < n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= cl)) (PreH20 : (cl <= UINT_MAX)) (PreH21 : ((Zlength (l_rp_2)) = i)) (PreH22 : (list_within_bound UINT_MOD l_rp_2 )) (PreH23 : (((list_to_Z (UINT_MOD) (l_rp_2)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))) (PreH24 : (n_pre > 0)) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (0 <= vl_pre)) (PreH27 : (vl_pre <= UINT_MAX)) (PreH28 : ((Zlength (l)) = n_pre)) (PreH29 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i l_rp_2 )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  EX (l_rp: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ (0 <= w0_value) ” 
  &&  “ (w0_value <= UINT_MAX) ” 
  &&  “ (0 <= w1_value) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ ((Zlength (l_rp)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre )) ” 
  &&  “ (((w1_value * UINT_MOD ) + w0_value ) = ((Znth i l 0) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i l_rp )
  **  (UIntArray.undef_seg rp_pre i n_pre )
.

Definition mpn_mul_1_entail_wit_5_1 := 
(
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l: (@list Z)) (l_rp_2: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits ((lpl + cl )) (32)) >= cl)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= cl)) (PreH5 : (cl <= UINT_MAX)) (PreH6 : (0 <= lpl)) (PreH7 : (lpl <= UINT_MAX)) (PreH8 : (0 <= hpl)) (PreH9 : (hpl <= UINT_MAX)) (PreH10 : ((Zlength (l_rp_2)) = i)) (PreH11 : (list_within_bound UINT_MOD l_rp_2 )) (PreH12 : (((list_to_Z (UINT_MOD) (l_rp_2)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))) (PreH13 : (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre ))) (PreH14 : (n_pre > 0)) (PreH15 : (n_pre <= INT_MAX)) (PreH16 : (0 <= vl_pre)) (PreH17 : (vl_pre <= UINT_MAX)) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.seg rp_pre 0 (i + 1 ) (app (l_rp_2) ((cons ((unsigned_last_nbits ((lpl + cl )) (32))) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  ((( &( "lpl" ) )) # UInt  |-> (unsigned_last_nbits ((lpl + cl )) (32)))
  **  ((( &( "hpl" ) )) # UInt  |-> hpl)
  **  ((( &( "ul" ) )) # UInt  |-> (Znth i l 0))
  **  (UIntArray.full up_pre n_pre l )
|--
  EX (l_rp: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (0 + hpl )) ” 
  &&  “ ((0 + hpl ) <= UINT_MAX) ” 
  &&  “ ((Zlength (l_rp)) = (i + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + ((0 + hpl ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 (i + 1 ) l_rp )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  ((( &( "lpl" ) )) # UInt  |->_)
  **  ((( &( "hpl" ) )) # UInt  |->_)
  **  ((( &( "ul" ) )) # UInt  |->_)
) \/
(
forall (vl_pre: Z) (n_pre: Z) (l: (@list Z)) (l_rp_2: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits ((lpl + cl )) (32)) >= cl)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= cl)) (PreH5 : (cl <= UINT_MAX)) (PreH6 : (0 <= lpl)) (PreH7 : (lpl <= UINT_MAX)) (PreH8 : (0 <= hpl)) (PreH9 : (hpl <= UINT_MAX)) (PreH10 : ((Zlength (l_rp_2)) = i)) (PreH11 : (list_within_bound UINT_MOD l_rp_2 )) (PreH12 : (((list_to_Z (UINT_MOD) (l_rp_2)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))) (PreH13 : (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre ))) (PreH14 : (n_pre > 0)) (PreH15 : (n_pre <= INT_MAX)) (PreH16 : (0 <= vl_pre)) (PreH17 : (vl_pre <= UINT_MAX)) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (list_within_bound UINT_MOD l )) ,
  TT && emp 
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (0 + hpl )) ” 
  &&  “ ((0 + hpl ) <= UINT_MAX) ” 
  &&  “ ((Zlength ((app (l_rp_2) ((cons ((unsigned_last_nbits ((lpl + cl )) (32))) ((@nil Z))))))) = (i + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD (app (l_rp_2) ((cons ((unsigned_last_nbits ((lpl + cl )) (32))) ((@nil Z))))) ) ” 
  &&  “ (((list_to_Z (UINT_MOD) ((app (l_rp_2) ((cons ((unsigned_last_nbits ((lpl + cl )) (32))) ((@nil Z))))))) + ((0 + hpl ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  emp
).

Definition mpn_mul_1_entail_wit_5_2 := 
(
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l: (@list Z)) (l_rp_2: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits ((lpl + cl )) (32)) < cl)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= cl)) (PreH5 : (cl <= UINT_MAX)) (PreH6 : (0 <= lpl)) (PreH7 : (lpl <= UINT_MAX)) (PreH8 : (0 <= hpl)) (PreH9 : (hpl <= UINT_MAX)) (PreH10 : ((Zlength (l_rp_2)) = i)) (PreH11 : (list_within_bound UINT_MOD l_rp_2 )) (PreH12 : (((list_to_Z (UINT_MOD) (l_rp_2)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))) (PreH13 : (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre ))) (PreH14 : (n_pre > 0)) (PreH15 : (n_pre <= INT_MAX)) (PreH16 : (0 <= vl_pre)) (PreH17 : (vl_pre <= UINT_MAX)) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.seg rp_pre 0 (i + 1 ) (app (l_rp_2) ((cons ((unsigned_last_nbits ((lpl + cl )) (32))) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  ((( &( "lpl" ) )) # UInt  |-> (unsigned_last_nbits ((lpl + cl )) (32)))
  **  ((( &( "hpl" ) )) # UInt  |-> hpl)
  **  ((( &( "ul" ) )) # UInt  |-> (Znth i l 0))
  **  (UIntArray.full up_pre n_pre l )
|--
  EX (l_rp: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (unsigned_last_nbits ((1 + hpl )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((1 + hpl )) (32)) <= UINT_MAX) ” 
  &&  “ ((Zlength (l_rp)) = (i + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + ((unsigned_last_nbits ((1 + hpl )) (32)) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 (i + 1 ) l_rp )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  ((( &( "lpl" ) )) # UInt  |->_)
  **  ((( &( "hpl" ) )) # UInt  |->_)
  **  ((( &( "ul" ) )) # UInt  |->_)
) \/
(
forall (vl_pre: Z) (n_pre: Z) (l: (@list Z)) (l_rp_2: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits ((lpl + cl )) (32)) < cl)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= cl)) (PreH5 : (cl <= UINT_MAX)) (PreH6 : (0 <= lpl)) (PreH7 : (lpl <= UINT_MAX)) (PreH8 : (0 <= hpl)) (PreH9 : (hpl <= UINT_MAX)) (PreH10 : ((Zlength (l_rp_2)) = i)) (PreH11 : (list_within_bound UINT_MOD l_rp_2 )) (PreH12 : (((list_to_Z (UINT_MOD) (l_rp_2)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))) (PreH13 : (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre ))) (PreH14 : (n_pre > 0)) (PreH15 : (n_pre <= INT_MAX)) (PreH16 : (0 <= vl_pre)) (PreH17 : (vl_pre <= UINT_MAX)) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (list_within_bound UINT_MOD l )) ,
  TT && emp 
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (unsigned_last_nbits ((1 + hpl )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((1 + hpl )) (32)) <= UINT_MAX) ” 
  &&  “ ((Zlength ((app (l_rp_2) ((cons ((unsigned_last_nbits ((lpl + cl )) (32))) ((@nil Z))))))) = (i + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD (app (l_rp_2) ((cons ((unsigned_last_nbits ((lpl + cl )) (32))) ((@nil Z))))) ) ” 
  &&  “ (((list_to_Z (UINT_MOD) ((app (l_rp_2) ((cons ((unsigned_last_nbits ((lpl + cl )) (32))) ((@nil Z))))))) + ((unsigned_last_nbits ((1 + hpl )) (32)) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  emp
).

Definition mpn_mul_1_return_wit_1 := 
(
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l: (@list Z)) (l_rp: (@list Z)) (cl: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= cl)) (PreH5 : (cl <= UINT_MAX)) (PreH6 : ((Zlength (l_rp)) = i)) (PreH7 : (list_within_bound UINT_MOD l_rp )) (PreH8 : (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))) (PreH9 : (n_pre > 0)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (0 <= vl_pre)) (PreH12 : (vl_pre <= UINT_MAX)) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i l_rp )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  EX (val': Z)  (l': (@list Z)) ,
  “ ((Zlength (l')) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val') ” 
  &&  “ ((val' + (cl * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l)) * vl_pre )) ”
  &&  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.full rp_pre n_pre l' )
) \/
(
forall (vl_pre: Z) (n_pre: Z) (rp_pre: Z) (l: (@list Z)) (l_rp: (@list Z)) (cl: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= cl)) (PreH5 : (cl <= UINT_MAX)) (PreH6 : ((Zlength (l_rp)) = i)) (PreH7 : (list_within_bound UINT_MOD l_rp )) (PreH8 : (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))) (PreH9 : (n_pre > 0)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (0 <= vl_pre)) (PreH12 : (vl_pre <= UINT_MAX)) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.seg rp_pre 0 i l_rp )
|--
  EX (l': (@list Z)) ,
  “ ((Zlength (l')) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l')) + (cl * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l)) * vl_pre )) ”
  &&  (UIntArray.full rp_pre n_pre l' )
).

Definition mpn_mul_1_partial_solve_wit_1 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l: (@list Z)) (l_rp: (@list Z)) (cl: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= cl)) (PreH5 : (cl <= UINT_MAX)) (PreH6 : ((Zlength (l_rp)) = i)) (PreH7 : (list_within_bound UINT_MOD l_rp )) (PreH8 : (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))) (PreH9 : (n_pre > 0)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (0 <= vl_pre)) (PreH12 : (vl_pre <= UINT_MAX)) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i l_rp )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_rp)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (((up_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth i l 0))
  **  (UIntArray.missing_i up_pre i 0 n_pre l )
  **  (UIntArray.seg rp_pre 0 i l_rp )
  **  (UIntArray.undef_seg rp_pre i n_pre )
.

Definition mpn_mul_1_partial_solve_wit_2 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l: (@list Z)) (l_rp: (@list Z)) (cl: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= cl)) (PreH5 : (cl <= UINT_MAX)) (PreH6 : ((Zlength (l_rp)) = i)) (PreH7 : (list_within_bound UINT_MOD l_rp )) (PreH8 : (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))) (PreH9 : (n_pre > 0)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (0 <= vl_pre)) (PreH12 : (vl_pre <= UINT_MAX)) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i l_rp )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_rp)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i l_rp )
  **  (UIntArray.undef_seg rp_pre i n_pre )
.

Definition mpn_mul_1_partial_solve_wit_3 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l: (@list Z)) (l_rp: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits ((lpl + cl )) (32)) >= cl)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= cl)) (PreH5 : (cl <= UINT_MAX)) (PreH6 : (0 <= lpl)) (PreH7 : (lpl <= UINT_MAX)) (PreH8 : (0 <= hpl)) (PreH9 : (hpl <= UINT_MAX)) (PreH10 : ((Zlength (l_rp)) = i)) (PreH11 : (list_within_bound UINT_MOD l_rp )) (PreH12 : (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))) (PreH13 : (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre ))) (PreH14 : (n_pre > 0)) (PreH15 : (n_pre <= INT_MAX)) (PreH16 : (0 <= vl_pre)) (PreH17 : (vl_pre <= UINT_MAX)) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (list_within_bound UINT_MOD l )) ,
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
  &&  “ ((Zlength (l_rp)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre )) ” 
  &&  “ (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i l_rp )
.

Definition mpn_mul_1_partial_solve_wit_4 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l: (@list Z)) (l_rp: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits ((lpl + cl )) (32)) < cl)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= cl)) (PreH5 : (cl <= UINT_MAX)) (PreH6 : (0 <= lpl)) (PreH7 : (lpl <= UINT_MAX)) (PreH8 : (0 <= hpl)) (PreH9 : (hpl <= UINT_MAX)) (PreH10 : ((Zlength (l_rp)) = i)) (PreH11 : (list_within_bound UINT_MOD l_rp )) (PreH12 : (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre ))) (PreH13 : (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre ))) (PreH14 : (n_pre > 0)) (PreH15 : (n_pre <= INT_MAX)) (PreH16 : (0 <= vl_pre)) (PreH17 : (vl_pre <= UINT_MAX)) (PreH18 : ((Zlength (l)) = n_pre)) (PreH19 : (list_within_bound UINT_MOD l )) ,
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
  &&  “ ((Zlength (l_rp)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_rp)) + (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) * vl_pre )) ” 
  &&  “ (((hpl * UINT_MOD ) + lpl ) = ((Znth i l 0) * vl_pre )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full up_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i l_rp )
.

(*----- Function mpn_sub_1 -----*)

Definition mpn_sub_1_safety_wit_1 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH3 : (list_within_bound UINT_MOD l )) (PreH4 : (n_pre > 0)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre <= UINT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.full ap_pre n_pre l )
  **  ((( &( "b" ) )) # UInt  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_sub_1_safety_wit_2 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (PreH1 : ((Znth 0 l 0) >= b_pre)) (PreH2 : ((Zlength (l)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH4 : (list_within_bound UINT_MOD l )) (PreH5 : (n_pre > 0)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= UINT_MAX)) ,
  (((rp_pre + (0 * sizeof(UINT)))) # UInt  |-> ((Znth 0 l 0) - b_pre ))
  **  (UIntArray.undef_seg rp_pre 1 n_pre )
  **  ((( &( "cy" ) )) # UInt  |-> 0)
  **  (UIntArray.full ap_pre n_pre l )
  **  ((( &( "a" ) )) # UInt  |-> (Znth 0 l 0))
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "b" ) )) # UInt  |-> 0)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  “ ((0 + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (0 + 1 )) ”
.

Definition mpn_sub_1_safety_wit_3 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (PreH1 : ((Znth 0 l 0) < b_pre)) (PreH2 : ((Zlength (l)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH4 : (list_within_bound UINT_MOD l )) (PreH5 : (n_pre > 0)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= UINT_MAX)) ,
  (((rp_pre + (0 * sizeof(UINT)))) # UInt  |-> (unsigned_last_nbits (((Znth 0 l 0) - b_pre )) (32)))
  **  (UIntArray.undef_seg rp_pre 1 n_pre )
  **  ((( &( "cy" ) )) # UInt  |-> 1)
  **  (UIntArray.full ap_pre n_pre l )
  **  ((( &( "a" ) )) # UInt  |-> (Znth 0 l 0))
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "b" ) )) # UInt  |-> 1)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  “ ((0 + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (0 + 1 )) ”
.

Definition mpn_sub_1_safety_wit_4 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (data_rp_partial: (@list Z)) (b: Z) (i: Z) (PreH1 : ((Znth i l 0) >= b)) (PreH2 : (i < n_pre)) (PreH3 : (0 < i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b <= 1)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (data_rp_partial)) = i)) (PreH9 : (list_within_bound UINT_MOD l )) (PreH10 : (list_within_bound UINT_MOD data_rp_partial )) (PreH11 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH12 : (((list_to_Z (UINT_MOD) (data_rp_partial)) - (b * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) - b_pre ))) ,
  (UIntArray.seg rp_pre 0 (i + 1 ) (app (data_rp_partial) ((cons (((Znth i l 0) - b )) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  ((( &( "cy" ) )) # UInt  |-> 0)
  **  (UIntArray.full ap_pre n_pre l )
  **  ((( &( "a" ) )) # UInt  |-> (Znth i l 0))
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "b" ) )) # UInt  |-> 0)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_sub_1_safety_wit_5 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (data_rp_partial: (@list Z)) (b: Z) (i: Z) (PreH1 : ((Znth i l 0) < b)) (PreH2 : (i < n_pre)) (PreH3 : (0 < i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b <= 1)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (data_rp_partial)) = i)) (PreH9 : (list_within_bound UINT_MOD l )) (PreH10 : (list_within_bound UINT_MOD data_rp_partial )) (PreH11 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH12 : (((list_to_Z (UINT_MOD) (data_rp_partial)) - (b * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) - b_pre ))) ,
  (UIntArray.seg rp_pre 0 (i + 1 ) (app (data_rp_partial) ((cons ((unsigned_last_nbits (((Znth i l 0) - b )) (32))) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  ((( &( "cy" ) )) # UInt  |-> 1)
  **  (UIntArray.full ap_pre n_pre l )
  **  ((( &( "a" ) )) # UInt  |-> (Znth i l 0))
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "b" ) )) # UInt  |-> 1)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_sub_1_entail_wit_1_1 := 
(
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (data_rp_partial_2: (@list Z)) (b: Z) (i: Z) (PreH1 : ((Znth i l 0) >= b)) (PreH2 : (i < n_pre)) (PreH3 : (0 < i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b <= 1)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (data_rp_partial_2)) = i)) (PreH9 : (list_within_bound UINT_MOD l )) (PreH10 : (list_within_bound UINT_MOD data_rp_partial_2 )) (PreH11 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH12 : (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (b * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) - b_pre ))) ,
  (UIntArray.seg rp_pre 0 (i + 1 ) (app (data_rp_partial_2) ((cons (((Znth i l 0) - b )) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l )
|--
  EX (data_rp_partial: (@list Z)) ,
  “ (0 < (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = (i + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (0 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) - b_pre )) ”
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 (i + 1 ) data_rp_partial )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
) \/
(
forall (b_pre: Z) (n_pre: Z) (val: Z) (l: (@list Z)) (data_rp_partial_2: (@list Z)) (b: Z) (i: Z) (PreH1 : ((Znth i l 0) >= b)) (PreH2 : (i < n_pre)) (PreH3 : (0 < i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b <= 1)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (data_rp_partial_2)) = i)) (PreH9 : (list_within_bound UINT_MOD l )) (PreH10 : (list_within_bound UINT_MOD data_rp_partial_2 )) (PreH11 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH12 : (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (b * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) - b_pre ))) ,
  TT && emp 
|--
  “ (((list_to_Z (UINT_MOD) ((app (data_rp_partial_2) ((cons (((Znth i l 0) - b )) ((@nil Z))))))) - (0 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) - b_pre )) ” 
  &&  “ (list_within_bound UINT_MOD (app (data_rp_partial_2) ((cons (((Znth i l 0) - b )) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((app (data_rp_partial_2) ((cons (((Znth i l 0) - b )) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition mpn_sub_1_entail_wit_1_1_split_goal_1 := 
forall (b_pre: Z) (n_pre: Z) (val: Z) (l: (@list Z)) (data_rp_partial_2: (@list Z)) (b: Z) (i: Z) (PreH1 : ((Znth i l 0) >= b)) (PreH2 : (i < n_pre)) (PreH3 : (0 < i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b <= 1)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (data_rp_partial_2)) = i)) (PreH9 : (list_within_bound UINT_MOD l )) (PreH10 : (list_within_bound UINT_MOD data_rp_partial_2 )) (PreH11 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH12 : (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (b * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) - b_pre ))) ,
  (((list_to_Z (UINT_MOD) ((app (data_rp_partial_2) ((cons (((Znth i l 0) - b )) ((@nil Z))))))) - (0 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) - b_pre ))
.

Definition mpn_sub_1_entail_wit_1_1_split_goal_2 := 
forall (b_pre: Z) (n_pre: Z) (val: Z) (l: (@list Z)) (data_rp_partial_2: (@list Z)) (b: Z) (i: Z) (PreH1 : ((Znth i l 0) >= b)) (PreH2 : (i < n_pre)) (PreH3 : (0 < i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b <= 1)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (data_rp_partial_2)) = i)) (PreH9 : (list_within_bound UINT_MOD l )) (PreH10 : (list_within_bound UINT_MOD data_rp_partial_2 )) (PreH11 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH12 : (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (b * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) - b_pre ))) ,
  (list_within_bound UINT_MOD (app (data_rp_partial_2) ((cons (((Znth i l 0) - b )) ((@nil Z))))) )
.

Definition mpn_sub_1_entail_wit_1_1_split_goal_3 := 
forall (b_pre: Z) (n_pre: Z) (val: Z) (l: (@list Z)) (data_rp_partial_2: (@list Z)) (b: Z) (i: Z) (PreH1 : ((Znth i l 0) >= b)) (PreH2 : (i < n_pre)) (PreH3 : (0 < i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b <= 1)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (data_rp_partial_2)) = i)) (PreH9 : (list_within_bound UINT_MOD l )) (PreH10 : (list_within_bound UINT_MOD data_rp_partial_2 )) (PreH11 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH12 : (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (b * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) - b_pre ))) ,
  ((Zlength ((app (data_rp_partial_2) ((cons (((Znth i l 0) - b )) ((@nil Z))))))) = (i + 1 ))
.

Definition mpn_sub_1_entail_wit_1_2 := 
(
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (data_rp_partial_2: (@list Z)) (b: Z) (i: Z) (PreH1 : ((Znth i l 0) < b)) (PreH2 : (i < n_pre)) (PreH3 : (0 < i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b <= 1)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (data_rp_partial_2)) = i)) (PreH9 : (list_within_bound UINT_MOD l )) (PreH10 : (list_within_bound UINT_MOD data_rp_partial_2 )) (PreH11 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH12 : (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (b * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) - b_pre ))) ,
  (UIntArray.seg rp_pre 0 (i + 1 ) (app (data_rp_partial_2) ((cons ((unsigned_last_nbits (((Znth i l 0) - b )) (32))) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l )
|--
  EX (data_rp_partial: (@list Z)) ,
  “ (0 < (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = (i + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (1 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) - b_pre )) ”
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 (i + 1 ) data_rp_partial )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
) \/
(
forall (b_pre: Z) (n_pre: Z) (val: Z) (l: (@list Z)) (data_rp_partial_2: (@list Z)) (b: Z) (i: Z) (PreH1 : ((Znth i l 0) < b)) (PreH2 : (i < n_pre)) (PreH3 : (0 < i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b <= 1)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (data_rp_partial_2)) = i)) (PreH9 : (list_within_bound UINT_MOD l )) (PreH10 : (list_within_bound UINT_MOD data_rp_partial_2 )) (PreH11 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH12 : (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (b * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) - b_pre ))) ,
  TT && emp 
|--
  “ (((list_to_Z (UINT_MOD) ((app (data_rp_partial_2) ((cons ((unsigned_last_nbits (((Znth i l 0) - b )) (32))) ((@nil Z))))))) - (1 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) - b_pre )) ” 
  &&  “ (list_within_bound UINT_MOD (app (data_rp_partial_2) ((cons ((unsigned_last_nbits (((Znth i l 0) - b )) (32))) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((app (data_rp_partial_2) ((cons ((unsigned_last_nbits (((Znth i l 0) - b )) (32))) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition mpn_sub_1_entail_wit_1_2_split_goal_1 := 
forall (b_pre: Z) (n_pre: Z) (val: Z) (l: (@list Z)) (data_rp_partial_2: (@list Z)) (b: Z) (i: Z) (PreH1 : ((Znth i l 0) < b)) (PreH2 : (i < n_pre)) (PreH3 : (0 < i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b <= 1)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (data_rp_partial_2)) = i)) (PreH9 : (list_within_bound UINT_MOD l )) (PreH10 : (list_within_bound UINT_MOD data_rp_partial_2 )) (PreH11 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH12 : (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (b * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) - b_pre ))) ,
  (((list_to_Z (UINT_MOD) ((app (data_rp_partial_2) ((cons ((unsigned_last_nbits (((Znth i l 0) - b )) (32))) ((@nil Z))))))) - (1 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) - b_pre ))
.

Definition mpn_sub_1_entail_wit_1_2_split_goal_2 := 
forall (b_pre: Z) (n_pre: Z) (val: Z) (l: (@list Z)) (data_rp_partial_2: (@list Z)) (b: Z) (i: Z) (PreH1 : ((Znth i l 0) < b)) (PreH2 : (i < n_pre)) (PreH3 : (0 < i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b <= 1)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (data_rp_partial_2)) = i)) (PreH9 : (list_within_bound UINT_MOD l )) (PreH10 : (list_within_bound UINT_MOD data_rp_partial_2 )) (PreH11 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH12 : (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (b * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) - b_pre ))) ,
  (list_within_bound UINT_MOD (app (data_rp_partial_2) ((cons ((unsigned_last_nbits (((Znth i l 0) - b )) (32))) ((@nil Z))))) )
.

Definition mpn_sub_1_entail_wit_1_2_split_goal_3 := 
forall (b_pre: Z) (n_pre: Z) (val: Z) (l: (@list Z)) (data_rp_partial_2: (@list Z)) (b: Z) (i: Z) (PreH1 : ((Znth i l 0) < b)) (PreH2 : (i < n_pre)) (PreH3 : (0 < i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b <= 1)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (data_rp_partial_2)) = i)) (PreH9 : (list_within_bound UINT_MOD l )) (PreH10 : (list_within_bound UINT_MOD data_rp_partial_2 )) (PreH11 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH12 : (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (b * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) - b_pre ))) ,
  ((Zlength ((app (data_rp_partial_2) ((cons ((unsigned_last_nbits (((Znth i l 0) - b )) (32))) ((@nil Z))))))) = (i + 1 ))
.

Definition mpn_sub_1_entail_wit_2_1 := 
(
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (PreH1 : ((Znth 0 l 0) >= b_pre)) (PreH2 : ((Zlength (l)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH4 : (list_within_bound UINT_MOD l )) (PreH5 : (n_pre > 0)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= UINT_MAX)) ,
  (((rp_pre + (0 * sizeof(UINT)))) # UInt  |-> ((Znth 0 l 0) - b_pre ))
  **  (UIntArray.undef_seg rp_pre 1 n_pre )
  **  (UIntArray.full ap_pre n_pre l )
|--
  EX (data_rp_partial: (@list Z)) ,
  “ (0 < (0 + 1 )) ” 
  &&  “ ((0 + 1 ) <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = (0 + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (0 * (Z.pow (UINT_MOD) ((0 + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((0 + 1 )) (l)))) - b_pre )) ”
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 (0 + 1 ) data_rp_partial )
  **  (UIntArray.undef_seg rp_pre (0 + 1 ) n_pre )
) \/
(
forall (b_pre: Z) (n_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (PreH1 : (((Znth 0 l 0) - b_pre ) <= UINT_MAX)) (PreH2 : (((Znth 0 l 0) - b_pre ) >= 0)) (PreH3 : ((Znth 0 l 0) >= b_pre)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH6 : (list_within_bound UINT_MOD l )) (PreH7 : (n_pre > 0)) (PreH8 : (0 <= b_pre)) (PreH9 : (b_pre <= UINT_MAX)) ,
  (((rp_pre + (0 * sizeof(UINT)))) # UInt  |-> ((Znth 0 l 0) - b_pre ))
|--
  EX (data_rp_partial: (@list Z)) ,
  “ (0 < (0 + 1 )) ” 
  &&  “ ((0 + 1 ) <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = (0 + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (0 * (Z.pow (UINT_MOD) ((0 + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((0 + 1 )) (l)))) - b_pre )) ”
  &&  (UIntArray.seg rp_pre 0 (0 + 1 ) data_rp_partial )
).

Definition mpn_sub_1_entail_wit_2_2 := 
(
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (PreH1 : ((Znth 0 l 0) < b_pre)) (PreH2 : ((Zlength (l)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH4 : (list_within_bound UINT_MOD l )) (PreH5 : (n_pre > 0)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= UINT_MAX)) ,
  (((rp_pre + (0 * sizeof(UINT)))) # UInt  |-> (unsigned_last_nbits (((Znth 0 l 0) - b_pre )) (32)))
  **  (UIntArray.undef_seg rp_pre 1 n_pre )
  **  (UIntArray.full ap_pre n_pre l )
|--
  EX (data_rp_partial: (@list Z)) ,
  “ (0 < (0 + 1 )) ” 
  &&  “ ((0 + 1 ) <= n_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = (0 + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (1 * (Z.pow (UINT_MOD) ((0 + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((0 + 1 )) (l)))) - b_pre )) ”
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 (0 + 1 ) data_rp_partial )
  **  (UIntArray.undef_seg rp_pre (0 + 1 ) n_pre )
) \/
(
forall (b_pre: Z) (n_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (PreH1 : ((unsigned_last_nbits (((Znth 0 l 0) - b_pre )) (32)) <= UINT_MAX)) (PreH2 : ((unsigned_last_nbits (((Znth 0 l 0) - b_pre )) (32)) >= 0)) (PreH3 : ((Znth 0 l 0) < b_pre)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH6 : (list_within_bound UINT_MOD l )) (PreH7 : (n_pre > 0)) (PreH8 : (0 <= b_pre)) (PreH9 : (b_pre <= UINT_MAX)) ,
  (((rp_pre + (0 * sizeof(UINT)))) # UInt  |-> (unsigned_last_nbits (((Znth 0 l 0) - b_pre )) (32)))
|--
  EX (data_rp_partial: (@list Z)) ,
  “ (0 < (0 + 1 )) ” 
  &&  “ ((0 + 1 ) <= n_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = (0 + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (1 * (Z.pow (UINT_MOD) ((0 + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((0 + 1 )) (l)))) - b_pre )) ”
  &&  (UIntArray.seg rp_pre 0 (0 + 1 ) data_rp_partial )
).

Definition mpn_sub_1_return_wit_1 := 
(
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (data_rp_partial: (@list Z)) (b: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 < i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= b)) (PreH5 : (b <= 1)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (data_rp_partial)) = i)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : (list_within_bound UINT_MOD data_rp_partial )) (PreH10 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH11 : (((list_to_Z (UINT_MOD) (data_rp_partial)) - (b * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) - b_pre ))) ,
  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  EX (val': Z) ,
  “ ((val' - (b * (Z.pow (UINT_MOD) (n_pre)) ) ) = (val - b_pre )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val n_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val' n_pre )
) \/
(
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (data_rp_partial: (@list Z)) (b: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 < i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= b)) (PreH5 : (b <= 1)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (data_rp_partial)) = i)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : (list_within_bound UINT_MOD data_rp_partial )) (PreH10 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH11 : (((list_to_Z (UINT_MOD) (data_rp_partial)) - (b * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) - b_pre ))) ,
  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
|--
  EX (val': Z) ,
  “ ((val' - (b * (Z.pow (UINT_MOD) (n_pre)) ) ) = (val - b_pre )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val n_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val' n_pre )
).

Definition mpn_sub_1_partial_solve_wit_1 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (PreH1 : (n_pre > 0)) (PreH2 : (0 <= b_pre)) (PreH3 : (b_pre <= UINT_MAX)) ,
  (mpd_store_Z UINT_MOD ap_pre val n_pre )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (n_pre > 0) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= UINT_MAX) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val n_pre )
  **  (UIntArray.undef_full rp_pre n_pre )
.

Definition mpn_sub_1_partial_solve_wit_2 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH3 : (list_within_bound UINT_MOD l )) (PreH4 : (n_pre > 0)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre <= UINT_MAX)) ,
  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= UINT_MAX) ”
  &&  (((ap_pre + (0 * sizeof(UINT)))) # UInt  |-> (Znth 0 l 0))
  **  (UIntArray.missing_i ap_pre 0 0 n_pre l )
  **  (UIntArray.undef_full rp_pre n_pre )
.

Definition mpn_sub_1_partial_solve_wit_3 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (PreH1 : ((Znth 0 l 0) >= b_pre)) (PreH2 : ((Zlength (l)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH4 : (list_within_bound UINT_MOD l )) (PreH5 : (n_pre > 0)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= UINT_MAX)) ,
  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ ((Znth 0 l 0) >= b_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= UINT_MAX) ”
  &&  (((rp_pre + (0 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre 1 n_pre )
  **  (UIntArray.full ap_pre n_pre l )
.

Definition mpn_sub_1_partial_solve_wit_4 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (PreH1 : ((Znth 0 l 0) < b_pre)) (PreH2 : ((Zlength (l)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH4 : (list_within_bound UINT_MOD l )) (PreH5 : (n_pre > 0)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= UINT_MAX)) ,
  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ ((Znth 0 l 0) < b_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= UINT_MAX) ”
  &&  (((rp_pre + (0 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre 1 n_pre )
  **  (UIntArray.full ap_pre n_pre l )
.

Definition mpn_sub_1_partial_solve_wit_5 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (data_rp_partial: (@list Z)) (b: Z) (i: Z) (PreH1 : ((Znth i l 0) >= b)) (PreH2 : (i < n_pre)) (PreH3 : (0 < i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b <= 1)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (data_rp_partial)) = i)) (PreH9 : (list_within_bound UINT_MOD l )) (PreH10 : (list_within_bound UINT_MOD data_rp_partial )) (PreH11 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH12 : (((list_to_Z (UINT_MOD) (data_rp_partial)) - (b * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) - b_pre ))) ,
  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ ((Znth i l 0) >= b) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 < i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b <= 1) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (b * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) - b_pre )) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
.

Definition mpn_sub_1_partial_solve_wit_6 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (data_rp_partial: (@list Z)) (b: Z) (i: Z) (PreH1 : ((Znth i l 0) < b)) (PreH2 : (i < n_pre)) (PreH3 : (0 < i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b <= 1)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (data_rp_partial)) = i)) (PreH9 : (list_within_bound UINT_MOD l )) (PreH10 : (list_within_bound UINT_MOD data_rp_partial )) (PreH11 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH12 : (((list_to_Z (UINT_MOD) (data_rp_partial)) - (b * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) - b_pre ))) ,
  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ ((Znth i l 0) < b) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 < i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b <= 1) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (b * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) - b_pre )) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
.

Definition mpn_sub_1_partial_solve_wit_7 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (data_rp_partial: (@list Z)) (b: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= b)) (PreH5 : (b <= 1)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (data_rp_partial)) = i)) (PreH8 : (list_within_bound UINT_MOD l )) (PreH9 : (list_within_bound UINT_MOD data_rp_partial )) (PreH10 : ((list_to_Z (UINT_MOD) (l)) = val)) (PreH11 : (((list_to_Z (UINT_MOD) (data_rp_partial)) - (b * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) - b_pre ))) ,
  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (0 < i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b <= 1) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (b * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) - b_pre )) ”
  &&  (((ap_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth i l 0))
  **  (UIntArray.missing_i ap_pre i 0 n_pre l )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
  **  (UIntArray.undef_seg rp_pre i n_pre )
.

Definition mpn_sub_1_which_implies_wit_1 := 
(
forall (val: Z) (n: Z) (ap: Z) ,
  (mpd_store_Z UINT_MOD ap val n )
|--
  EX (l: (@list Z)) ,
  “ ((Zlength (l)) = n) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full ap n l )
) \/
(
forall (val: Z) (n: Z) (ap: Z) ,
  (mpd_store_Z UINT_MOD ap val n )
|--
  EX (l: (@list Z)) ,
  “ ((Zlength (l)) = n) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full ap n l )
).

(*----- Function mpn_sub_n -----*)

Definition mpn_sub_n_safety_wit_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (PreH1 : ((Zlength (l_a)) = n_pre)) (PreH2 : ((Zlength (l_b)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH4 : (list_within_bound UINT_MOD l_a )) (PreH5 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH6 : (list_within_bound UINT_MOD l_b )) (PreH7 : (n_pre >= 0)) ,
  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.full bp_pre n_pre l_b )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_sub_n_safety_wit_2 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (PreH1 : ((Zlength (l_a)) = n_pre)) (PreH2 : ((Zlength (l_b)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH4 : (list_within_bound UINT_MOD l_a )) (PreH5 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH6 : (list_within_bound UINT_MOD l_b )) (PreH7 : (n_pre >= 0)) ,
  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.full bp_pre n_pre l_b )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_sub_n_safety_wit_3 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial: (@list Z)) (cy: Z) (i: Z) (PreH1 : ((Znth i l_a 0) >= (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)))) (PreH2 : ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((Zlength (l_a)) = n_pre)) (PreH9 : ((Zlength (l_b)) = n_pre)) (PreH10 : ((Zlength (data_rp_partial)) = i)) (PreH11 : (list_within_bound UINT_MOD l_a )) (PreH12 : (list_within_bound UINT_MOD l_b )) (PreH13 : (list_within_bound UINT_MOD data_rp_partial )) (PreH14 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH15 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH16 : (((list_to_Z (UINT_MOD) (data_rp_partial)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) ))) ,
  (UIntArray.seg rp_pre 0 (i + 1 ) (app (data_rp_partial) ((cons (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # UInt  |-> (0 + 0 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_sub_n_safety_wit_4 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial: (@list Z)) (cy: Z) (i: Z) (PreH1 : ((Znth i l_a 0) < (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)))) (PreH2 : ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((Zlength (l_a)) = n_pre)) (PreH9 : ((Zlength (l_b)) = n_pre)) (PreH10 : ((Zlength (data_rp_partial)) = i)) (PreH11 : (list_within_bound UINT_MOD l_a )) (PreH12 : (list_within_bound UINT_MOD l_b )) (PreH13 : (list_within_bound UINT_MOD data_rp_partial )) (PreH14 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH15 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH16 : (((list_to_Z (UINT_MOD) (data_rp_partial)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) ))) ,
  (UIntArray.seg rp_pre 0 (i + 1 ) (app (data_rp_partial) ((cons ((unsigned_last_nbits (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) (32))) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # UInt  |-> (0 + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_sub_n_safety_wit_5 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial: (@list Z)) (cy: Z) (i: Z) (PreH1 : ((Znth i l_a 0) >= (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)))) (PreH2 : ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((Zlength (l_a)) = n_pre)) (PreH9 : ((Zlength (l_b)) = n_pre)) (PreH10 : ((Zlength (data_rp_partial)) = i)) (PreH11 : (list_within_bound UINT_MOD l_a )) (PreH12 : (list_within_bound UINT_MOD l_b )) (PreH13 : (list_within_bound UINT_MOD data_rp_partial )) (PreH14 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH15 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH16 : (((list_to_Z (UINT_MOD) (data_rp_partial)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) ))) ,
  (UIntArray.seg rp_pre 0 (i + 1 ) (app (data_rp_partial) ((cons (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # UInt  |-> (1 + 0 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_sub_n_safety_wit_6 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial: (@list Z)) (cy: Z) (i: Z) (PreH1 : ((Znth i l_a 0) < (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)))) (PreH2 : ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((Zlength (l_a)) = n_pre)) (PreH9 : ((Zlength (l_b)) = n_pre)) (PreH10 : ((Zlength (data_rp_partial)) = i)) (PreH11 : (list_within_bound UINT_MOD l_a )) (PreH12 : (list_within_bound UINT_MOD l_b )) (PreH13 : (list_within_bound UINT_MOD data_rp_partial )) (PreH14 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH15 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH16 : (((list_to_Z (UINT_MOD) (data_rp_partial)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) ))) ,
  (UIntArray.seg rp_pre 0 (i + 1 ) (app (data_rp_partial) ((cons ((unsigned_last_nbits (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) (32))) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # UInt  |-> (1 + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_sub_n_entail_wit_1 := 
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (PreH1 : ((Zlength (l_a)) = n_pre)) (PreH2 : ((Zlength (l_b)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH4 : (list_within_bound UINT_MOD l_a )) (PreH5 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH6 : (list_within_bound UINT_MOD l_b )) (PreH7 : (n_pre >= 0)) ,
  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  EX (data_rp_partial: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = 0) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (0 * (Z.pow (UINT_MOD) (0)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (0) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (0) (l_b)))) )) ”
  &&  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre 0 0 data_rp_partial )
  **  (UIntArray.undef_seg rp_pre 0 n_pre )
) \/
(
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (PreH1 : ((Zlength (l_a)) = n_pre)) (PreH2 : ((Zlength (l_b)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH4 : (list_within_bound UINT_MOD l_a )) (PreH5 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH6 : (list_within_bound UINT_MOD l_b )) (PreH7 : (n_pre >= 0)) ,
  TT && emp 
|--
  “ (((list_to_Z (UINT_MOD) ((@nil Z))) - (0 * (Z.pow (UINT_MOD) (0)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (0) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (0) (l_b)))) )) ” 
  &&  “ (list_within_bound UINT_MOD (@nil Z) ) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ”
  &&  emp
).

Definition mpn_sub_n_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (PreH1 : ((Zlength (l_a)) = n_pre)) (PreH2 : ((Zlength (l_b)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH4 : (list_within_bound UINT_MOD l_a )) (PreH5 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH6 : (list_within_bound UINT_MOD l_b )) (PreH7 : (n_pre >= 0)) ,
  (((list_to_Z (UINT_MOD) ((@nil Z))) - (0 * (Z.pow (UINT_MOD) (0)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (0) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (0) (l_b)))) ))
.

Definition mpn_sub_n_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (PreH1 : ((Zlength (l_a)) = n_pre)) (PreH2 : ((Zlength (l_b)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH4 : (list_within_bound UINT_MOD l_a )) (PreH5 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH6 : (list_within_bound UINT_MOD l_b )) (PreH7 : (n_pre >= 0)) ,
  (list_within_bound UINT_MOD (@nil Z) )
.

Definition mpn_sub_n_entail_wit_1_split_goal_3 := 
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (PreH1 : ((Zlength (l_a)) = n_pre)) (PreH2 : ((Zlength (l_b)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH4 : (list_within_bound UINT_MOD l_a )) (PreH5 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH6 : (list_within_bound UINT_MOD l_b )) (PreH7 : (n_pre >= 0)) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition mpn_sub_n_entail_wit_2_1 := 
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial_2: (@list Z)) (cy: Z) (i: Z) (PreH1 : ((Znth i l_a 0) >= (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)))) (PreH2 : ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((Zlength (l_a)) = n_pre)) (PreH9 : ((Zlength (l_b)) = n_pre)) (PreH10 : ((Zlength (data_rp_partial_2)) = i)) (PreH11 : (list_within_bound UINT_MOD l_a )) (PreH12 : (list_within_bound UINT_MOD l_b )) (PreH13 : (list_within_bound UINT_MOD data_rp_partial_2 )) (PreH14 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH15 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH16 : (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) ))) ,
  (UIntArray.seg rp_pre 0 (i + 1 ) (app (data_rp_partial_2) ((cons (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
|--
  EX (data_rp_partial: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (0 + 0 )) ” 
  &&  “ ((0 + 0 ) <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = (i + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - ((0 + 0 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) )) ”
  &&  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre 0 (i + 1 ) data_rp_partial )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
) \/
(
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial_2: (@list Z)) (cy: Z) (i: Z) (PreH1 : ((Znth i l_a 0) >= (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)))) (PreH2 : ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((Zlength (l_a)) = n_pre)) (PreH9 : ((Zlength (l_b)) = n_pre)) (PreH10 : ((Zlength (data_rp_partial_2)) = i)) (PreH11 : (list_within_bound UINT_MOD l_a )) (PreH12 : (list_within_bound UINT_MOD l_b )) (PreH13 : (list_within_bound UINT_MOD data_rp_partial_2 )) (PreH14 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH15 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH16 : (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) ))) ,
  TT && emp 
|--
  “ (((list_to_Z (UINT_MOD) ((app (data_rp_partial_2) ((cons (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) ((@nil Z))))))) - ((0 + 0 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) )) ” 
  &&  “ (list_within_bound UINT_MOD (app (data_rp_partial_2) ((cons (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((app (data_rp_partial_2) ((cons (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition mpn_sub_n_entail_wit_2_1_split_goal_1 := 
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial_2: (@list Z)) (cy: Z) (i: Z) (PreH1 : ((Znth i l_a 0) >= (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)))) (PreH2 : ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((Zlength (l_a)) = n_pre)) (PreH9 : ((Zlength (l_b)) = n_pre)) (PreH10 : ((Zlength (data_rp_partial_2)) = i)) (PreH11 : (list_within_bound UINT_MOD l_a )) (PreH12 : (list_within_bound UINT_MOD l_b )) (PreH13 : (list_within_bound UINT_MOD data_rp_partial_2 )) (PreH14 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH15 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH16 : (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) ))) ,
  (((list_to_Z (UINT_MOD) ((app (data_rp_partial_2) ((cons (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) ((@nil Z))))))) - ((0 + 0 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) ))
.

Definition mpn_sub_n_entail_wit_2_1_split_goal_2 := 
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial_2: (@list Z)) (cy: Z) (i: Z) (PreH1 : ((Znth i l_a 0) >= (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)))) (PreH2 : ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((Zlength (l_a)) = n_pre)) (PreH9 : ((Zlength (l_b)) = n_pre)) (PreH10 : ((Zlength (data_rp_partial_2)) = i)) (PreH11 : (list_within_bound UINT_MOD l_a )) (PreH12 : (list_within_bound UINT_MOD l_b )) (PreH13 : (list_within_bound UINT_MOD data_rp_partial_2 )) (PreH14 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH15 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH16 : (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) ))) ,
  (list_within_bound UINT_MOD (app (data_rp_partial_2) ((cons (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) ((@nil Z))))) )
.

Definition mpn_sub_n_entail_wit_2_1_split_goal_3 := 
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial_2: (@list Z)) (cy: Z) (i: Z) (PreH1 : ((Znth i l_a 0) >= (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)))) (PreH2 : ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((Zlength (l_a)) = n_pre)) (PreH9 : ((Zlength (l_b)) = n_pre)) (PreH10 : ((Zlength (data_rp_partial_2)) = i)) (PreH11 : (list_within_bound UINT_MOD l_a )) (PreH12 : (list_within_bound UINT_MOD l_b )) (PreH13 : (list_within_bound UINT_MOD data_rp_partial_2 )) (PreH14 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH15 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH16 : (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) ))) ,
  ((Zlength ((app (data_rp_partial_2) ((cons (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) ((@nil Z))))))) = (i + 1 ))
.

Definition mpn_sub_n_entail_wit_2_2 := 
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial_2: (@list Z)) (cy: Z) (i: Z) (PreH1 : ((Znth i l_a 0) < (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)))) (PreH2 : ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((Zlength (l_a)) = n_pre)) (PreH9 : ((Zlength (l_b)) = n_pre)) (PreH10 : ((Zlength (data_rp_partial_2)) = i)) (PreH11 : (list_within_bound UINT_MOD l_a )) (PreH12 : (list_within_bound UINT_MOD l_b )) (PreH13 : (list_within_bound UINT_MOD data_rp_partial_2 )) (PreH14 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH15 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH16 : (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) ))) ,
  (UIntArray.seg rp_pre 0 (i + 1 ) (app (data_rp_partial_2) ((cons ((unsigned_last_nbits (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) (32))) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
|--
  EX (data_rp_partial: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (0 + 1 )) ” 
  &&  “ ((0 + 1 ) <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = (i + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - ((0 + 1 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) )) ”
  &&  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre 0 (i + 1 ) data_rp_partial )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
) \/
(
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial_2: (@list Z)) (cy: Z) (i: Z) (PreH1 : ((Znth i l_a 0) < (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)))) (PreH2 : ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((Zlength (l_a)) = n_pre)) (PreH9 : ((Zlength (l_b)) = n_pre)) (PreH10 : ((Zlength (data_rp_partial_2)) = i)) (PreH11 : (list_within_bound UINT_MOD l_a )) (PreH12 : (list_within_bound UINT_MOD l_b )) (PreH13 : (list_within_bound UINT_MOD data_rp_partial_2 )) (PreH14 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH15 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH16 : (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) ))) ,
  TT && emp 
|--
  “ (((list_to_Z (UINT_MOD) ((app (data_rp_partial_2) ((cons ((unsigned_last_nbits (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) (32))) ((@nil Z))))))) - ((0 + 1 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) )) ” 
  &&  “ (list_within_bound UINT_MOD (app (data_rp_partial_2) ((cons ((unsigned_last_nbits (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) (32))) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((app (data_rp_partial_2) ((cons ((unsigned_last_nbits (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) (32))) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition mpn_sub_n_entail_wit_2_2_split_goal_1 := 
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial_2: (@list Z)) (cy: Z) (i: Z) (PreH1 : ((Znth i l_a 0) < (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)))) (PreH2 : ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((Zlength (l_a)) = n_pre)) (PreH9 : ((Zlength (l_b)) = n_pre)) (PreH10 : ((Zlength (data_rp_partial_2)) = i)) (PreH11 : (list_within_bound UINT_MOD l_a )) (PreH12 : (list_within_bound UINT_MOD l_b )) (PreH13 : (list_within_bound UINT_MOD data_rp_partial_2 )) (PreH14 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH15 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH16 : (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) ))) ,
  (((list_to_Z (UINT_MOD) ((app (data_rp_partial_2) ((cons ((unsigned_last_nbits (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) (32))) ((@nil Z))))))) - ((0 + 1 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) ))
.

Definition mpn_sub_n_entail_wit_2_2_split_goal_2 := 
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial_2: (@list Z)) (cy: Z) (i: Z) (PreH1 : ((Znth i l_a 0) < (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)))) (PreH2 : ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((Zlength (l_a)) = n_pre)) (PreH9 : ((Zlength (l_b)) = n_pre)) (PreH10 : ((Zlength (data_rp_partial_2)) = i)) (PreH11 : (list_within_bound UINT_MOD l_a )) (PreH12 : (list_within_bound UINT_MOD l_b )) (PreH13 : (list_within_bound UINT_MOD data_rp_partial_2 )) (PreH14 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH15 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH16 : (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) ))) ,
  (list_within_bound UINT_MOD (app (data_rp_partial_2) ((cons ((unsigned_last_nbits (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) (32))) ((@nil Z))))) )
.

Definition mpn_sub_n_entail_wit_2_2_split_goal_3 := 
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial_2: (@list Z)) (cy: Z) (i: Z) (PreH1 : ((Znth i l_a 0) < (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)))) (PreH2 : ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((Zlength (l_a)) = n_pre)) (PreH9 : ((Zlength (l_b)) = n_pre)) (PreH10 : ((Zlength (data_rp_partial_2)) = i)) (PreH11 : (list_within_bound UINT_MOD l_a )) (PreH12 : (list_within_bound UINT_MOD l_b )) (PreH13 : (list_within_bound UINT_MOD data_rp_partial_2 )) (PreH14 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH15 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH16 : (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) ))) ,
  ((Zlength ((app (data_rp_partial_2) ((cons ((unsigned_last_nbits (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) (32))) ((@nil Z))))))) = (i + 1 ))
.

Definition mpn_sub_n_entail_wit_2_3 := 
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial_2: (@list Z)) (cy: Z) (i: Z) (PreH1 : ((Znth i l_a 0) >= (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)))) (PreH2 : ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((Zlength (l_a)) = n_pre)) (PreH9 : ((Zlength (l_b)) = n_pre)) (PreH10 : ((Zlength (data_rp_partial_2)) = i)) (PreH11 : (list_within_bound UINT_MOD l_a )) (PreH12 : (list_within_bound UINT_MOD l_b )) (PreH13 : (list_within_bound UINT_MOD data_rp_partial_2 )) (PreH14 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH15 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH16 : (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) ))) ,
  (UIntArray.seg rp_pre 0 (i + 1 ) (app (data_rp_partial_2) ((cons (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
|--
  EX (data_rp_partial: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (1 + 0 )) ” 
  &&  “ ((1 + 0 ) <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = (i + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - ((1 + 0 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) )) ”
  &&  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre 0 (i + 1 ) data_rp_partial )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
) \/
(
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial_2: (@list Z)) (cy: Z) (i: Z) (PreH1 : ((Znth i l_a 0) >= (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)))) (PreH2 : ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((Zlength (l_a)) = n_pre)) (PreH9 : ((Zlength (l_b)) = n_pre)) (PreH10 : ((Zlength (data_rp_partial_2)) = i)) (PreH11 : (list_within_bound UINT_MOD l_a )) (PreH12 : (list_within_bound UINT_MOD l_b )) (PreH13 : (list_within_bound UINT_MOD data_rp_partial_2 )) (PreH14 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH15 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH16 : (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) ))) ,
  TT && emp 
|--
  “ (((list_to_Z (UINT_MOD) ((app (data_rp_partial_2) ((cons (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) ((@nil Z))))))) - ((1 + 0 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) )) ” 
  &&  “ (list_within_bound UINT_MOD (app (data_rp_partial_2) ((cons (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((app (data_rp_partial_2) ((cons (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition mpn_sub_n_entail_wit_2_3_split_goal_1 := 
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial_2: (@list Z)) (cy: Z) (i: Z) (PreH1 : ((Znth i l_a 0) >= (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)))) (PreH2 : ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((Zlength (l_a)) = n_pre)) (PreH9 : ((Zlength (l_b)) = n_pre)) (PreH10 : ((Zlength (data_rp_partial_2)) = i)) (PreH11 : (list_within_bound UINT_MOD l_a )) (PreH12 : (list_within_bound UINT_MOD l_b )) (PreH13 : (list_within_bound UINT_MOD data_rp_partial_2 )) (PreH14 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH15 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH16 : (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) ))) ,
  (((list_to_Z (UINT_MOD) ((app (data_rp_partial_2) ((cons (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) ((@nil Z))))))) - ((1 + 0 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) ))
.

Definition mpn_sub_n_entail_wit_2_3_split_goal_2 := 
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial_2: (@list Z)) (cy: Z) (i: Z) (PreH1 : ((Znth i l_a 0) >= (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)))) (PreH2 : ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((Zlength (l_a)) = n_pre)) (PreH9 : ((Zlength (l_b)) = n_pre)) (PreH10 : ((Zlength (data_rp_partial_2)) = i)) (PreH11 : (list_within_bound UINT_MOD l_a )) (PreH12 : (list_within_bound UINT_MOD l_b )) (PreH13 : (list_within_bound UINT_MOD data_rp_partial_2 )) (PreH14 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH15 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH16 : (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) ))) ,
  (list_within_bound UINT_MOD (app (data_rp_partial_2) ((cons (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) ((@nil Z))))) )
.

Definition mpn_sub_n_entail_wit_2_3_split_goal_3 := 
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial_2: (@list Z)) (cy: Z) (i: Z) (PreH1 : ((Znth i l_a 0) >= (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)))) (PreH2 : ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((Zlength (l_a)) = n_pre)) (PreH9 : ((Zlength (l_b)) = n_pre)) (PreH10 : ((Zlength (data_rp_partial_2)) = i)) (PreH11 : (list_within_bound UINT_MOD l_a )) (PreH12 : (list_within_bound UINT_MOD l_b )) (PreH13 : (list_within_bound UINT_MOD data_rp_partial_2 )) (PreH14 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH15 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH16 : (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) ))) ,
  ((Zlength ((app (data_rp_partial_2) ((cons (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) ((@nil Z))))))) = (i + 1 ))
.

Definition mpn_sub_n_entail_wit_2_4 := 
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial_2: (@list Z)) (cy: Z) (i: Z) (PreH1 : ((Znth i l_a 0) < (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)))) (PreH2 : ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((Zlength (l_a)) = n_pre)) (PreH9 : ((Zlength (l_b)) = n_pre)) (PreH10 : ((Zlength (data_rp_partial_2)) = i)) (PreH11 : (list_within_bound UINT_MOD l_a )) (PreH12 : (list_within_bound UINT_MOD l_b )) (PreH13 : (list_within_bound UINT_MOD data_rp_partial_2 )) (PreH14 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH15 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH16 : (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) ))) ,
  (UIntArray.seg rp_pre 0 (i + 1 ) (app (data_rp_partial_2) ((cons ((unsigned_last_nbits (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) (32))) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
|--
  EX (data_rp_partial: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (1 + 1 )) ” 
  &&  “ ((1 + 1 ) <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = (i + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - ((1 + 1 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) )) ”
  &&  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre 0 (i + 1 ) data_rp_partial )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
) \/
(
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial_2: (@list Z)) (cy: Z) (i: Z) (PreH1 : ((Znth i l_a 0) < (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)))) (PreH2 : ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((Zlength (l_a)) = n_pre)) (PreH9 : ((Zlength (l_b)) = n_pre)) (PreH10 : ((Zlength (data_rp_partial_2)) = i)) (PreH11 : (list_within_bound UINT_MOD l_a )) (PreH12 : (list_within_bound UINT_MOD l_b )) (PreH13 : (list_within_bound UINT_MOD data_rp_partial_2 )) (PreH14 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH15 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH16 : (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) ))) ,
  TT && emp 
|--
  “ (((list_to_Z (UINT_MOD) ((app (data_rp_partial_2) ((cons ((unsigned_last_nbits (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) (32))) ((@nil Z))))))) - ((1 + 1 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) )) ” 
  &&  “ (list_within_bound UINT_MOD (app (data_rp_partial_2) ((cons ((unsigned_last_nbits (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) (32))) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((app (data_rp_partial_2) ((cons ((unsigned_last_nbits (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) (32))) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition mpn_sub_n_entail_wit_2_4_split_goal_1 := 
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial_2: (@list Z)) (cy: Z) (i: Z) (PreH1 : ((Znth i l_a 0) < (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)))) (PreH2 : ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((Zlength (l_a)) = n_pre)) (PreH9 : ((Zlength (l_b)) = n_pre)) (PreH10 : ((Zlength (data_rp_partial_2)) = i)) (PreH11 : (list_within_bound UINT_MOD l_a )) (PreH12 : (list_within_bound UINT_MOD l_b )) (PreH13 : (list_within_bound UINT_MOD data_rp_partial_2 )) (PreH14 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH15 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH16 : (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) ))) ,
  (((list_to_Z (UINT_MOD) ((app (data_rp_partial_2) ((cons ((unsigned_last_nbits (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) (32))) ((@nil Z))))))) - ((1 + 1 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) ))
.

Definition mpn_sub_n_entail_wit_2_4_split_goal_2 := 
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial_2: (@list Z)) (cy: Z) (i: Z) (PreH1 : ((Znth i l_a 0) < (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)))) (PreH2 : ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((Zlength (l_a)) = n_pre)) (PreH9 : ((Zlength (l_b)) = n_pre)) (PreH10 : ((Zlength (data_rp_partial_2)) = i)) (PreH11 : (list_within_bound UINT_MOD l_a )) (PreH12 : (list_within_bound UINT_MOD l_b )) (PreH13 : (list_within_bound UINT_MOD data_rp_partial_2 )) (PreH14 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH15 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH16 : (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) ))) ,
  (list_within_bound UINT_MOD (app (data_rp_partial_2) ((cons ((unsigned_last_nbits (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) (32))) ((@nil Z))))) )
.

Definition mpn_sub_n_entail_wit_2_4_split_goal_3 := 
forall (n_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial_2: (@list Z)) (cy: Z) (i: Z) (PreH1 : ((Znth i l_a 0) < (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)))) (PreH2 : ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((Zlength (l_a)) = n_pre)) (PreH9 : ((Zlength (l_b)) = n_pre)) (PreH10 : ((Zlength (data_rp_partial_2)) = i)) (PreH11 : (list_within_bound UINT_MOD l_a )) (PreH12 : (list_within_bound UINT_MOD l_b )) (PreH13 : (list_within_bound UINT_MOD data_rp_partial_2 )) (PreH14 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH15 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH16 : (((list_to_Z (UINT_MOD) (data_rp_partial_2)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) ))) ,
  ((Zlength ((app (data_rp_partial_2) ((cons ((unsigned_last_nbits (((Znth i l_a 0) - (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) )) (32))) ((@nil Z))))))) = (i + 1 ))
.

Definition mpn_sub_n_return_wit_1 := 
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial: (@list Z)) (cy: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= cy)) (PreH5 : (cy <= 2)) (PreH6 : ((Zlength (l_a)) = n_pre)) (PreH7 : ((Zlength (l_b)) = n_pre)) (PreH8 : ((Zlength (data_rp_partial)) = i)) (PreH9 : (list_within_bound UINT_MOD l_a )) (PreH10 : (list_within_bound UINT_MOD l_b )) (PreH11 : (list_within_bound UINT_MOD data_rp_partial )) (PreH12 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH13 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH14 : (((list_to_Z (UINT_MOD) (data_rp_partial)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) ))) ,
  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  EX (val_r: Z) ,
  “ ((val_r - (cy * (Z.pow (UINT_MOD) (n_pre)) ) ) = (val_a - val_b )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a n_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b n_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r n_pre )
) \/
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial: (@list Z)) (cy: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= cy)) (PreH5 : (cy <= 2)) (PreH6 : ((Zlength (l_a)) = n_pre)) (PreH7 : ((Zlength (l_b)) = n_pre)) (PreH8 : ((Zlength (data_rp_partial)) = i)) (PreH9 : (list_within_bound UINT_MOD l_a )) (PreH10 : (list_within_bound UINT_MOD l_b )) (PreH11 : (list_within_bound UINT_MOD data_rp_partial )) (PreH12 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH13 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH14 : (((list_to_Z (UINT_MOD) (data_rp_partial)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) ))) ,
  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
|--
  EX (val_r: Z) ,
  “ ((val_r - (cy * (Z.pow (UINT_MOD) (n_pre)) ) ) = (val_a - val_b )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a n_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b n_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r n_pre )
).

Definition mpn_sub_n_partial_solve_wit_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (PreH1 : (n_pre >= 0)) ,
  (mpd_store_Z UINT_MOD ap_pre val_a n_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b n_pre )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (n_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a n_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b n_pre )
  **  (UIntArray.undef_full rp_pre n_pre )
.

Definition mpn_sub_n_partial_solve_wit_2 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial: (@list Z)) (cy: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= cy)) (PreH5 : (cy <= 2)) (PreH6 : ((Zlength (l_a)) = n_pre)) (PreH7 : ((Zlength (l_b)) = n_pre)) (PreH8 : ((Zlength (data_rp_partial)) = i)) (PreH9 : (list_within_bound UINT_MOD l_a )) (PreH10 : (list_within_bound UINT_MOD l_b )) (PreH11 : (list_within_bound UINT_MOD data_rp_partial )) (PreH12 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH13 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH14 : (((list_to_Z (UINT_MOD) (data_rp_partial)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) ))) ,
  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) )) ”
  &&  (((ap_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth i l_a 0))
  **  (UIntArray.missing_i ap_pre i 0 n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
  **  (UIntArray.undef_seg rp_pre i n_pre )
.

Definition mpn_sub_n_partial_solve_wit_3 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial: (@list Z)) (cy: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= cy)) (PreH5 : (cy <= 2)) (PreH6 : ((Zlength (l_a)) = n_pre)) (PreH7 : ((Zlength (l_b)) = n_pre)) (PreH8 : ((Zlength (data_rp_partial)) = i)) (PreH9 : (list_within_bound UINT_MOD l_a )) (PreH10 : (list_within_bound UINT_MOD l_b )) (PreH11 : (list_within_bound UINT_MOD data_rp_partial )) (PreH12 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH13 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH14 : (((list_to_Z (UINT_MOD) (data_rp_partial)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) ))) ,
  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) )) ”
  &&  (((bp_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth i l_b 0))
  **  (UIntArray.missing_i bp_pre i 0 n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
  **  (UIntArray.undef_seg rp_pre i n_pre )
.

Definition mpn_sub_n_partial_solve_wit_4 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial: (@list Z)) (cy: Z) (i: Z) (PreH1 : ((Znth i l_a 0) >= (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)))) (PreH2 : ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((Zlength (l_a)) = n_pre)) (PreH9 : ((Zlength (l_b)) = n_pre)) (PreH10 : ((Zlength (data_rp_partial)) = i)) (PreH11 : (list_within_bound UINT_MOD l_a )) (PreH12 : (list_within_bound UINT_MOD l_b )) (PreH13 : (list_within_bound UINT_MOD data_rp_partial )) (PreH14 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH15 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH16 : (((list_to_Z (UINT_MOD) (data_rp_partial)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) ))) ,
  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ ((Znth i l_a 0) >= (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) >= cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) )) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
.

Definition mpn_sub_n_partial_solve_wit_5 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial: (@list Z)) (cy: Z) (i: Z) (PreH1 : ((Znth i l_a 0) < (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)))) (PreH2 : ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((Zlength (l_a)) = n_pre)) (PreH9 : ((Zlength (l_b)) = n_pre)) (PreH10 : ((Zlength (data_rp_partial)) = i)) (PreH11 : (list_within_bound UINT_MOD l_a )) (PreH12 : (list_within_bound UINT_MOD l_b )) (PreH13 : (list_within_bound UINT_MOD data_rp_partial )) (PreH14 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH15 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH16 : (((list_to_Z (UINT_MOD) (data_rp_partial)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) ))) ,
  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ ((Znth i l_a 0) < (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) >= cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) )) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
.

Definition mpn_sub_n_partial_solve_wit_6 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial: (@list Z)) (cy: Z) (i: Z) (PreH1 : ((Znth i l_a 0) >= (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)))) (PreH2 : ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((Zlength (l_a)) = n_pre)) (PreH9 : ((Zlength (l_b)) = n_pre)) (PreH10 : ((Zlength (data_rp_partial)) = i)) (PreH11 : (list_within_bound UINT_MOD l_a )) (PreH12 : (list_within_bound UINT_MOD l_b )) (PreH13 : (list_within_bound UINT_MOD data_rp_partial )) (PreH14 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH15 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH16 : (((list_to_Z (UINT_MOD) (data_rp_partial)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) ))) ,
  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ ((Znth i l_a 0) >= (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) < cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) )) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
.

Definition mpn_sub_n_partial_solve_wit_7 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (data_rp_partial: (@list Z)) (cy: Z) (i: Z) (PreH1 : ((Znth i l_a 0) < (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)))) (PreH2 : ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((Zlength (l_a)) = n_pre)) (PreH9 : ((Zlength (l_b)) = n_pre)) (PreH10 : ((Zlength (data_rp_partial)) = i)) (PreH11 : (list_within_bound UINT_MOD l_a )) (PreH12 : (list_within_bound UINT_MOD l_b )) (PreH13 : (list_within_bound UINT_MOD data_rp_partial )) (PreH14 : ((list_to_Z (UINT_MOD) (l_a)) = val_a)) (PreH15 : ((list_to_Z (UINT_MOD) (l_b)) = val_b)) (PreH16 : (((list_to_Z (UINT_MOD) (data_rp_partial)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) ))) ,
  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ ((Znth i l_a 0) < (unsigned_last_nbits (((Znth i l_b 0) + cy )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_b 0) + cy )) (32)) < cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((Zlength (data_rp_partial)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (list_within_bound UINT_MOD data_rp_partial ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (((list_to_Z (UINT_MOD) (data_rp_partial)) - (cy * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) - (list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) )) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i data_rp_partial )
.

Definition mpn_sub_n_which_implies_wit_1 := 
(
forall (val_b: Z) (val_a: Z) (n: Z) (ap: Z) (bp: Z) ,
  (mpd_store_Z UINT_MOD ap val_a n )
  **  (mpd_store_Z UINT_MOD bp val_b n )
|--
  EX (l_b: (@list Z))  (l_a: (@list Z)) ,
  “ ((Zlength (l_a)) = n) ” 
  &&  “ ((Zlength (l_b)) = n) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ”
  &&  (UIntArray.full ap n l_a )
  **  (UIntArray.full bp n l_b )
) \/
(
forall (val_b: Z) (val_a: Z) (n: Z) (ap: Z) (bp: Z) ,
  (mpd_store_Z UINT_MOD ap val_a n )
  **  (mpd_store_Z UINT_MOD bp val_b n )
|--
  EX (l_b: (@list Z))  (l_a: (@list Z)) ,
  “ ((Zlength (l_a)) = n) ” 
  &&  “ ((Zlength (l_b)) = n) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ”
  &&  (UIntArray.full ap n l_a )
  **  (UIntArray.full bp n l_b )
).

(*----- Function mpn_sub -----*)

Definition mpn_sub_safety_wit_1 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_lo: Z) (val_a_hi: Z) (val_r: Z) (retval: Z) (l_r: (@list Z)) (PreH1 : (an_pre > bn_pre)) (PreH2 : ((an_pre - bn_pre ) > 0)) (PreH3 : (an_pre > bn_pre)) (PreH4 : (0 <= retval)) (PreH5 : (retval <= UINT_MAX)) (PreH6 : (an_pre <= INT_MAX)) (PreH7 : (bn_pre <= INT_MAX)) (PreH8 : (an_pre >= INT_MIN)) (PreH9 : (bn_pre >= INT_MIN)) (PreH10 : ((Zlength (l_r)) = bn_pre)) (PreH11 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH12 : (list_within_bound UINT_MOD l_r )) (PreH13 : ((val_r - (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_lo - val_b ))) (PreH14 : (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH15 : (an_pre >= bn_pre)) (PreH16 : (an_pre > 0)) (PreH17 : (bn_pre >= 0)) ,
  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "cy" ) )) # UInt  |-> retval)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_hi (an_pre - bn_pre ) )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
|--
  “ ((an_pre - bn_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (an_pre - bn_pre )) ”
.

Definition mpn_sub_entail_wit_1 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_lo: Z) (val_a_hi: Z) (val_r: Z) (retval: Z) (l_r: (@list Z)) (PreH1 : ((Zlength (l_r)) = bn_pre)) (PreH2 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH3 : (list_within_bound UINT_MOD l_r )) (PreH4 : ((val_r - (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_lo - val_b ))) (PreH5 : (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH6 : (an_pre >= bn_pre)) (PreH7 : (an_pre > 0)) (PreH8 : (bn_pre >= 0)) ,
  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_hi (an_pre - bn_pre ) )
  **  ((( &( "cy" ) )) # UInt  |-> retval)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (an_pre <= INT_MAX) ” 
  &&  “ (bn_pre <= INT_MAX) ” 
  &&  “ (an_pre >= INT_MIN) ” 
  &&  “ (bn_pre >= INT_MIN) ” 
  &&  “ ((Zlength (l_r)) = bn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((val_r - (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_lo - val_b )) ” 
  &&  “ (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre > 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  ((( &( "cy" ) )) # UInt  |-> retval)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_hi (an_pre - bn_pre ) )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
.

Definition mpn_sub_entail_wit_2 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_lo: Z) (val_a_hi: Z) (val_r: Z) (retval: Z) (l_r: (@list Z)) (PreH1 : (an_pre > bn_pre)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= UINT_MAX)) (PreH4 : (an_pre <= INT_MAX)) (PreH5 : (bn_pre <= INT_MAX)) (PreH6 : (an_pre >= INT_MIN)) (PreH7 : (bn_pre >= INT_MIN)) (PreH8 : ((Zlength (l_r)) = bn_pre)) (PreH9 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH10 : (list_within_bound UINT_MOD l_r )) (PreH11 : ((val_r - (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_lo - val_b ))) (PreH12 : (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH13 : (an_pre >= bn_pre)) (PreH14 : (an_pre > 0)) (PreH15 : (bn_pre >= 0)) ,
  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_hi (an_pre - bn_pre ) )
|--
  “ (an_pre > bn_pre) ” 
  &&  “ ((an_pre - bn_pre ) > 0) ” 
  &&  “ (an_pre > bn_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (an_pre <= INT_MAX) ” 
  &&  “ (bn_pre <= INT_MAX) ” 
  &&  “ (an_pre >= INT_MIN) ” 
  &&  “ (bn_pre >= INT_MIN) ” 
  &&  “ ((Zlength (l_r)) = bn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((val_r - (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_lo - val_b )) ” 
  &&  “ (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre > 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_hi (an_pre - bn_pre ) )
.

Definition mpn_sub_return_wit_1 := 
(
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_lo: Z) (val_a_hi: Z) (val_r: Z) (retval_2: Z) (l_r: (@list Z)) (val': Z) (retval: Z) (PreH1 : ((val' - (retval * (Z.pow (UINT_MOD) ((an_pre - bn_pre ))) ) ) = (val_a_hi - retval_2 ))) (PreH2 : (an_pre > bn_pre)) (PreH3 : ((an_pre - bn_pre ) > 0)) (PreH4 : (an_pre > bn_pre)) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= UINT_MAX)) (PreH7 : (an_pre <= INT_MAX)) (PreH8 : (bn_pre <= INT_MAX)) (PreH9 : (an_pre >= INT_MIN)) (PreH10 : (bn_pre >= INT_MIN)) (PreH11 : ((Zlength (l_r)) = bn_pre)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH13 : (list_within_bound UINT_MOD l_r )) (PreH14 : ((val_r - (retval_2 * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_lo - val_b ))) (PreH15 : (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH16 : (an_pre >= bn_pre)) (PreH17 : (an_pre > 0)) (PreH18 : (bn_pre >= 0)) ,
  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_hi (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (rp_pre + (bn_pre * sizeof(UINT))) val' (an_pre - bn_pre ) )
  **  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
|--
  EX (val_r_out: Z) ,
  “ ((val_r_out - (retval * (Z.pow (UINT_MOD) (an_pre)) ) ) = (val_a - val_b )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_out an_pre )
) \/
(
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_lo: Z) (val_a_hi: Z) (val_r: Z) (retval_2: Z) (l_r: (@list Z)) (val': Z) (retval: Z) (PreH1 : ((val' - (retval * (Z.pow (UINT_MOD) ((an_pre - bn_pre ))) ) ) = (val_a_hi - retval_2 ))) (PreH2 : (an_pre > bn_pre)) (PreH3 : ((an_pre - bn_pre ) > 0)) (PreH4 : (an_pre > bn_pre)) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= UINT_MAX)) (PreH7 : (an_pre <= INT_MAX)) (PreH8 : (bn_pre <= INT_MAX)) (PreH9 : (an_pre >= INT_MIN)) (PreH10 : (bn_pre >= INT_MIN)) (PreH11 : ((Zlength (l_r)) = bn_pre)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH13 : (list_within_bound UINT_MOD l_r )) (PreH14 : ((val_r - (retval_2 * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_lo - val_b ))) (PreH15 : (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH16 : (an_pre >= bn_pre)) (PreH17 : (an_pre > 0)) (PreH18 : (bn_pre >= 0)) ,
  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_hi (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (rp_pre + (bn_pre * sizeof(UINT))) val' (an_pre - bn_pre ) )
  **  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
|--
  EX (val_r_out: Z) ,
  “ ((val_r_out - (retval * (Z.pow (UINT_MOD) (an_pre)) ) ) = (val_a - val_b )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_out an_pre )
).

Definition mpn_sub_return_wit_2 := 
(
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_lo: Z) (val_a_hi: Z) (val_r: Z) (retval: Z) (l_r: (@list Z)) (PreH1 : (an_pre <= bn_pre)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= UINT_MAX)) (PreH4 : (an_pre <= INT_MAX)) (PreH5 : (bn_pre <= INT_MAX)) (PreH6 : (an_pre >= INT_MIN)) (PreH7 : (bn_pre >= INT_MIN)) (PreH8 : ((Zlength (l_r)) = bn_pre)) (PreH9 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH10 : (list_within_bound UINT_MOD l_r )) (PreH11 : ((val_r - (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_lo - val_b ))) (PreH12 : (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH13 : (an_pre >= bn_pre)) (PreH14 : (an_pre > 0)) (PreH15 : (bn_pre >= 0)) ,
  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_hi (an_pre - bn_pre ) )
|--
  EX (val_r_out: Z) ,
  “ ((val_r_out - (retval * (Z.pow (UINT_MOD) (an_pre)) ) ) = (val_a - val_b )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_out an_pre )
) \/
(
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_lo: Z) (val_a_hi: Z) (val_r: Z) (retval: Z) (l_r: (@list Z)) (PreH1 : (an_pre <= bn_pre)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= UINT_MAX)) (PreH4 : (an_pre <= INT_MAX)) (PreH5 : (bn_pre <= INT_MAX)) (PreH6 : (an_pre >= INT_MIN)) (PreH7 : (bn_pre >= INT_MIN)) (PreH8 : ((Zlength (l_r)) = bn_pre)) (PreH9 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH10 : (list_within_bound UINT_MOD l_r )) (PreH11 : ((val_r - (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_lo - val_b ))) (PreH12 : (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH13 : (an_pre >= bn_pre)) (PreH14 : (an_pre > 0)) (PreH15 : (bn_pre >= 0)) ,
  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_hi (an_pre - bn_pre ) )
|--
  EX (val_r_out: Z) ,
  “ ((val_r_out - (retval * (Z.pow (UINT_MOD) (an_pre)) ) ) = (val_a - val_b )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_out an_pre )
).

Definition mpn_sub_partial_solve_wit_1_pure := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (PreH1 : (an_pre >= bn_pre)) (PreH2 : (an_pre > 0)) (PreH3 : (bn_pre >= 0)) ,
  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (mpd_store_Z UINT_MOD ap_pre val_a an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full rp_pre an_pre )
|--
  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre > 0) ” 
  &&  “ (bn_pre >= 0) ”
.

Definition mpn_sub_partial_solve_wit_1_aux := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (PreH1 : (an_pre >= bn_pre)) (PreH2 : (an_pre > 0)) (PreH3 : (bn_pre >= 0)) ,
  (mpd_store_Z UINT_MOD ap_pre val_a an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full rp_pre an_pre )
|--
  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre > 0) ” 
  &&  “ (bn_pre >= 0) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre > 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full rp_pre an_pre )
.

Definition mpn_sub_partial_solve_wit_1 := mpn_sub_partial_solve_wit_1_pure -> mpn_sub_partial_solve_wit_1_aux.

Definition mpn_sub_partial_solve_wit_2_pure := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_lo: Z) (val_a_hi: Z) (PreH1 : (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH2 : (an_pre >= bn_pre)) (PreH3 : (an_pre > 0)) (PreH4 : (bn_pre >= 0)) ,
  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_hi (an_pre - bn_pre ) )
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full rp_pre an_pre )
|--
  “ (an_pre >= bn_pre) ” 
  &&  “ (bn_pre >= 0) ”
.

Definition mpn_sub_partial_solve_wit_2_aux := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_lo: Z) (val_a_hi: Z) (PreH1 : (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH2 : (an_pre >= bn_pre)) (PreH3 : (an_pre > 0)) (PreH4 : (bn_pre >= 0)) ,
  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_hi (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full rp_pre an_pre )
|--
  “ (an_pre >= bn_pre) ” 
  &&  “ (bn_pre >= 0) ” 
  &&  “ (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre > 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (UIntArray.undef_full rp_pre an_pre )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_hi (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
.

Definition mpn_sub_partial_solve_wit_2 := mpn_sub_partial_solve_wit_2_pure -> mpn_sub_partial_solve_wit_2_aux.

Definition mpn_sub_partial_solve_wit_3_pure := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_lo: Z) (val_a_hi: Z) (PreH1 : (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH2 : (an_pre >= bn_pre)) (PreH3 : (an_pre > 0)) (PreH4 : (bn_pre >= 0)) ,
  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.undef_full rp_pre bn_pre )
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_hi (an_pre - bn_pre ) )
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
|--
  “ (bn_pre >= 0) ”
.

Definition mpn_sub_partial_solve_wit_3_aux := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_lo: Z) (val_a_hi: Z) (PreH1 : (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH2 : (an_pre >= bn_pre)) (PreH3 : (an_pre > 0)) (PreH4 : (bn_pre >= 0)) ,
  (UIntArray.undef_full rp_pre bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_hi (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
|--
  “ (bn_pre >= 0) ” 
  &&  “ (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre > 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full rp_pre bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_hi (an_pre - bn_pre ) )
.

Definition mpn_sub_partial_solve_wit_3 := mpn_sub_partial_solve_wit_3_pure -> mpn_sub_partial_solve_wit_3_aux.

Definition mpn_sub_partial_solve_wit_4 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_lo: Z) (val_a_hi: Z) (val_r: Z) (retval: Z) (PreH1 : ((val_r - (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_lo - val_b ))) (PreH2 : (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH3 : (an_pre >= bn_pre)) (PreH4 : (an_pre > 0)) (PreH5 : (bn_pre >= 0)) ,
  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_hi (an_pre - bn_pre ) )
|--
  “ ((val_r - (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_lo - val_b )) ” 
  &&  “ (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre > 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD rp_pre val_r bn_pre )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_hi (an_pre - bn_pre ) )
.

Definition mpn_sub_partial_solve_wit_5_pure := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_lo: Z) (val_a_hi: Z) (val_r: Z) (retval: Z) (l_r: (@list Z)) (PreH1 : (an_pre > bn_pre)) (PreH2 : ((an_pre - bn_pre ) > 0)) (PreH3 : (an_pre > bn_pre)) (PreH4 : (0 <= retval)) (PreH5 : (retval <= UINT_MAX)) (PreH6 : (an_pre <= INT_MAX)) (PreH7 : (bn_pre <= INT_MAX)) (PreH8 : (an_pre >= INT_MIN)) (PreH9 : (bn_pre >= INT_MIN)) (PreH10 : ((Zlength (l_r)) = bn_pre)) (PreH11 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH12 : (list_within_bound UINT_MOD l_r )) (PreH13 : ((val_r - (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_lo - val_b ))) (PreH14 : (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH15 : (an_pre >= bn_pre)) (PreH16 : (an_pre > 0)) (PreH17 : (bn_pre >= 0)) ,
  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "cy" ) )) # UInt  |-> retval)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_hi (an_pre - bn_pre ) )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
|--
  “ ((an_pre - bn_pre ) > 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ”
.

Definition mpn_sub_partial_solve_wit_5_aux := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_lo: Z) (val_a_hi: Z) (val_r: Z) (retval: Z) (l_r: (@list Z)) (PreH1 : (an_pre > bn_pre)) (PreH2 : ((an_pre - bn_pre ) > 0)) (PreH3 : (an_pre > bn_pre)) (PreH4 : (0 <= retval)) (PreH5 : (retval <= UINT_MAX)) (PreH6 : (an_pre <= INT_MAX)) (PreH7 : (bn_pre <= INT_MAX)) (PreH8 : (an_pre >= INT_MIN)) (PreH9 : (bn_pre >= INT_MIN)) (PreH10 : ((Zlength (l_r)) = bn_pre)) (PreH11 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH12 : (list_within_bound UINT_MOD l_r )) (PreH13 : ((val_r - (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_lo - val_b ))) (PreH14 : (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) ))) (PreH15 : (an_pre >= bn_pre)) (PreH16 : (an_pre > 0)) (PreH17 : (bn_pre >= 0)) ,
  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_hi (an_pre - bn_pre ) )
|--
  “ ((an_pre - bn_pre ) > 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (an_pre > bn_pre) ” 
  &&  “ ((an_pre - bn_pre ) > 0) ” 
  &&  “ (an_pre > bn_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= UINT_MAX) ” 
  &&  “ (an_pre <= INT_MAX) ” 
  &&  “ (bn_pre <= INT_MAX) ” 
  &&  “ (an_pre >= INT_MIN) ” 
  &&  “ (bn_pre >= INT_MIN) ” 
  &&  “ ((Zlength (l_r)) = bn_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ ((val_r - (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_lo - val_b )) ” 
  &&  “ (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn_pre)) ) )) ” 
  &&  “ (an_pre >= bn_pre) ” 
  &&  “ (an_pre > 0) ” 
  &&  “ (bn_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT))) val_a_hi (an_pre - bn_pre ) )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT))) (an_pre - bn_pre ) )
  **  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_lo bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
.

Definition mpn_sub_partial_solve_wit_5 := mpn_sub_partial_solve_wit_5_pure -> mpn_sub_partial_solve_wit_5_aux.

Definition mpn_sub_which_implies_wit_1 := 
(
forall (val_a: Z) (an: Z) (bn: Z) (ap: Z) (PreH1 : (an >= bn)) (PreH2 : (an > 0)) (PreH3 : (bn >= 0)) ,
  (mpd_store_Z UINT_MOD ap val_a an )
|--
  EX (val_a_hi: Z)  (val_a_lo: Z) ,
  “ (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn)) ) )) ”
  &&  (mpd_store_Z UINT_MOD ap val_a_lo bn )
  **  (mpd_store_Z UINT_MOD (ap + (bn * sizeof(UINT))) val_a_hi (an - bn ) )
) \/
(
forall (val_a: Z) (an: Z) (bn: Z) (ap: Z) (PreH1 : (an >= bn)) (PreH2 : (an > 0)) (PreH3 : (bn >= 0)) ,
  (mpd_store_Z UINT_MOD ap val_a an )
|--
  EX (val_a_hi: Z)  (val_a_lo: Z) ,
  “ (val_a = (val_a_lo + (val_a_hi * (Z.pow (UINT_MOD) (bn)) ) )) ”
  &&  (mpd_store_Z UINT_MOD ap val_a_lo bn )
  **  (mpd_store_Z UINT_MOD (ap + (bn * sizeof(UINT))) val_a_hi (an - bn ) )
).

Definition mpn_sub_which_implies_wit_2 := 
(
forall (an: Z) (bn: Z) (rp: Z) (PreH1 : (an >= bn)) (PreH2 : (bn >= 0)) ,
  (UIntArray.undef_full rp an )
|--
  (UIntArray.undef_full rp bn )
  **  (UIntArray.undef_full (rp + (bn * sizeof(UINT))) (an - bn ) )
) \/
(
forall (an: Z) (bn: Z) (rp: Z) (PreH1 : (an >= bn)) (PreH2 : (bn >= 0)) ,
  (UIntArray.undef_full rp an )
|--
  (UIntArray.undef_full rp bn )
  **  (UIntArray.undef_full (rp + (bn * sizeof(UINT))) (an - bn ) )
).

Definition mpn_sub_which_implies_wit_2_split_goal_spatial := 
forall (an: Z) (bn: Z) (rp: Z) (PreH1 : (an >= bn)) (PreH2 : (bn >= 0)) ,
  (UIntArray.undef_full rp an )
|--
  (UIntArray.undef_full rp bn )
  **  (UIntArray.undef_full (rp + (bn * sizeof(UINT))) (an - bn ) )
.

Definition mpn_sub_which_implies_wit_3 := 
(
forall (val_r_out: Z) (bn: Z) (rp: Z) ,
  (mpd_store_Z UINT_MOD rp val_r_out bn )
|--
  EX (l_r: (@list Z)) ,
  “ ((Zlength (l_r)) = bn) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r_out) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ”
  &&  (UIntArray.full rp bn l_r )
) \/
(
forall (val_r_out: Z) (bn: Z) (rp: Z) ,
  (mpd_store_Z UINT_MOD rp val_r_out bn )
|--
  EX (l_r: (@list Z)) ,
  “ ((Zlength (l_r)) = bn) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r_out) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ”
  &&  (UIntArray.full rp bn l_r )
).

(*----- Function mpz_clear -----*)

Definition mpz_clear_return_wit_1 := 
forall (r_pre: Z) (n: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign n size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (cap_2 <> 0)) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
|--
  EX (ptr: Z)  (cap: Z)  (size: Z) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_clear_return_wit_2 := 
(
forall (r_pre: Z) (n: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign n size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (cap_2 = 0)) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (n)) (Zabs (size_2)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
|--
  EX (ptr: Z)  (cap: Z)  (size: Z) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
) \/
(
forall (n: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign n size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (cap_2 = 0)) ,
  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (n)) (Zabs (size_2)) )
|--
  TT && emp 
).

Definition mpz_clear_return_wit_2_split_goal_spatial := 
forall (n: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign n size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (cap_2 = 0)) ,
  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (n)) (Zabs (size_2)) )
|--
  TT && emp 
.

Definition mpz_clear_partial_solve_wit_1 := 
forall (r_pre: Z) (n: Z) ,
  (store_Z r_pre n )
|--
  EX (cap: Z)  (size: Z)  (ptr: Z) ,
  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
.

Definition mpz_clear_partial_solve_wit_2 := 
forall (r_pre: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign n size )) (PreH2 : ((Zabs (size)) <= cap)) (PreH3 : (cap <> 0)) ,
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

(*----- Function mpz_realloc -----*)

Definition mpz_realloc_safety_wit_1 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (PreH1 : (size_pre >= cap)) (PreH2 : (size_pre <= INT_MAX)) (PreH3 : (cap >= 0)) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zabs (old)) <= cap)) (PreH6 : (same_sign n old )) ,
  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpz_realloc_safety_wit_2 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 > retval)) (PreH2 : (retval_3 = (Zabs (old)))) (PreH3 : (retval = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap >= 0)) (PreH7 : (cap <= INT_MAX)) (PreH8 : ((Zabs (old)) <= cap)) (PreH9 : (same_sign n old )) (PreH10 : (cap <> 0)) ,
  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (old)) retval )
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_realloc_safety_wit_3 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 > retval)) (PreH2 : (retval_3 = (Zabs (old)))) (PreH3 : (retval = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap >= 0)) (PreH7 : (cap <= INT_MAX)) (PreH8 : ((Zabs (old)) <= cap)) (PreH9 : (same_sign n old )) (PreH10 : (cap = 0)) ,
  (UIntArray.undef_full retval_2 retval )
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_realloc_return_wit_1 := 
(
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 <= retval_2)) (PreH2 : (retval_3 = (Zabs (old)))) (PreH3 : (retval_2 = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap >= 0)) (PreH7 : (cap <= INT_MAX)) (PreH8 : ((Zabs (old)) <= cap)) (PreH9 : (same_sign n old )) (PreH10 : (cap = 0)) ,
  (UIntArray.undef_full retval retval_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
|--
  EX (r_pre__mp_alloc: Z) ,
  “ (same_sign n old ) ” 
  &&  “ (r_pre__mp_alloc = (Z.max (size_pre) (1))) ”
  &&  (mpd_store_Z_compact UINT_MOD retval (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval (Zabs (old)) (Z.max (size_pre) (1)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
) \/
(
forall (size_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 <= retval_2)) (PreH2 : (retval_3 = (Zabs (old)))) (PreH3 : (retval_2 = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap >= 0)) (PreH7 : (cap <= INT_MAX)) (PreH8 : ((Zabs (old)) <= cap)) (PreH9 : (same_sign n old )) (PreH10 : (cap = 0)) ,
  (UIntArray.undef_full retval retval_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
|--
  (mpd_store_Z_compact UINT_MOD retval (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval (Zabs (old)) (Z.max (size_pre) (1)) )
).

Definition mpz_realloc_return_wit_1_split_goal_spatial := 
forall (size_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 <= retval_2)) (PreH2 : (retval_3 = (Zabs (old)))) (PreH3 : (retval_2 = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap >= 0)) (PreH7 : (cap <= INT_MAX)) (PreH8 : ((Zabs (old)) <= cap)) (PreH9 : (same_sign n old )) (PreH10 : (cap = 0)) ,
  (UIntArray.undef_full retval retval_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
|--
  (mpd_store_Z_compact UINT_MOD retval (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval (Zabs (old)) (Z.max (size_pre) (1)) )
.

Definition mpz_realloc_return_wit_2 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (retval_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 <= retval_2)) (PreH2 : (retval_3 = (Zabs (old)))) (PreH3 : (retval_2 = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap >= 0)) (PreH7 : (cap <= INT_MAX)) (PreH8 : ((Zabs (old)) <= cap)) (PreH9 : (same_sign n old )) (PreH10 : (cap <> 0)) ,
  (mpd_store_Z_compact UINT_MOD retval (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval (Zabs (old)) retval_2 )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
|--
  EX (r_pre__mp_alloc: Z) ,
  “ (same_sign n old ) ” 
  &&  “ (r_pre__mp_alloc = (Z.max (size_pre) (1))) ”
  &&  (mpd_store_Z_compact UINT_MOD retval (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval (Zabs (old)) (Z.max (size_pre) (1)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
.

Definition mpz_realloc_return_wit_3 := 
(
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 > retval_2)) (PreH2 : (retval_3 = (Zabs (old)))) (PreH3 : (retval_2 = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap >= 0)) (PreH7 : (cap <= INT_MAX)) (PreH8 : ((Zabs (old)) <= cap)) (PreH9 : (same_sign n old )) (PreH10 : (cap = 0)) ,
  (UIntArray.undef_full retval retval_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
|--
  EX (r_pre__mp_alloc: Z) ,
  “ (same_sign n old ) ” 
  &&  “ (r_pre__mp_alloc = (Z.max (size_pre) (1))) ”
  &&  (mpd_store_Z_compact UINT_MOD retval (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval (Zabs (old)) (Z.max (size_pre) (1)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
) \/
(
forall (size_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 > retval_2)) (PreH2 : (retval_3 = (Zabs (old)))) (PreH3 : (retval_2 = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap >= 0)) (PreH7 : (cap <= INT_MAX)) (PreH8 : ((Zabs (old)) <= cap)) (PreH9 : (same_sign n old )) (PreH10 : (cap = 0)) ,
  (UIntArray.undef_full retval retval_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
|--
  “ (0 = old) ”
  &&  (mpd_store_Z_compact UINT_MOD retval (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval (Zabs (old)) (Z.max (size_pre) (1)) )
).

Definition mpz_realloc_return_wit_3_split_goal_1 := 
forall (size_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 > retval_2)) (PreH2 : (retval_3 = (Zabs (old)))) (PreH3 : (retval_2 = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap >= 0)) (PreH7 : (cap <= INT_MAX)) (PreH8 : ((Zabs (old)) <= cap)) (PreH9 : (same_sign n old )) (PreH10 : (cap = 0)) ,
  (UIntArray.undef_full retval retval_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
|--
  “ (0 = old) ”
.

Definition mpz_realloc_return_wit_3_split_goal_spatial := 
forall (size_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 > retval_2)) (PreH2 : (retval_3 = (Zabs (old)))) (PreH3 : (retval_2 = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap >= 0)) (PreH7 : (cap <= INT_MAX)) (PreH8 : ((Zabs (old)) <= cap)) (PreH9 : (same_sign n old )) (PreH10 : (cap = 0)) ,
  (UIntArray.undef_full retval retval_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
|--
  (mpd_store_Z_compact UINT_MOD retval (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval (Zabs (old)) (Z.max (size_pre) (1)) )
.

Definition mpz_realloc_return_wit_4 := 
(
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (retval_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 > retval_2)) (PreH2 : (retval_3 = (Zabs (old)))) (PreH3 : (retval_2 = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap >= 0)) (PreH7 : (cap <= INT_MAX)) (PreH8 : ((Zabs (old)) <= cap)) (PreH9 : (same_sign n old )) (PreH10 : (cap <> 0)) ,
  (mpd_store_Z_compact UINT_MOD retval (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval (Zabs (old)) retval_2 )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
|--
  EX (r_pre__mp_alloc: Z) ,
  “ (same_sign n old ) ” 
  &&  “ (r_pre__mp_alloc = (Z.max (size_pre) (1))) ”
  &&  (mpd_store_Z_compact UINT_MOD retval (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval (Zabs (old)) (Z.max (size_pre) (1)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
) \/
(
forall (size_pre: Z) (n: Z) (cap: Z) (old: Z) (retval_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 > retval_2)) (PreH2 : (retval_3 = (Zabs (old)))) (PreH3 : (retval_2 = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap >= 0)) (PreH7 : (cap <= INT_MAX)) (PreH8 : ((Zabs (old)) <= cap)) (PreH9 : (same_sign n old )) (PreH10 : (cap <> 0)) ,
  (mpd_store_Z_compact UINT_MOD retval (Zabs (n)) (Zabs (old)) )
|--
  “ (0 = old) ”
  &&  (mpd_store_Z_compact UINT_MOD retval (Zabs (n)) (Zabs (old)) )
).

Definition mpz_realloc_return_wit_4_split_goal_1 := 
forall (size_pre: Z) (n: Z) (cap: Z) (old: Z) (retval_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 > retval_2)) (PreH2 : (retval_3 = (Zabs (old)))) (PreH3 : (retval_2 = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap >= 0)) (PreH7 : (cap <= INT_MAX)) (PreH8 : ((Zabs (old)) <= cap)) (PreH9 : (same_sign n old )) (PreH10 : (cap <> 0)) ,
  (mpd_store_Z_compact UINT_MOD retval (Zabs (n)) (Zabs (old)) )
|--
  “ (0 = old) ”
.

Definition mpz_realloc_return_wit_4_split_goal_spatial := 
forall (size_pre: Z) (n: Z) (cap: Z) (old: Z) (retval_2: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 > retval_2)) (PreH2 : (retval_3 = (Zabs (old)))) (PreH3 : (retval_2 = (Z.max (size_pre) (1)))) (PreH4 : (size_pre >= cap)) (PreH5 : (size_pre <= INT_MAX)) (PreH6 : (cap >= 0)) (PreH7 : (cap <= INT_MAX)) (PreH8 : ((Zabs (old)) <= cap)) (PreH9 : (same_sign n old )) (PreH10 : (cap <> 0)) ,
  (mpd_store_Z_compact UINT_MOD retval (Zabs (n)) (Zabs (old)) )
|--
  (mpd_store_Z_compact UINT_MOD retval (Zabs (n)) (Zabs (old)) )
.

Definition mpz_realloc_partial_solve_wit_1 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (PreH1 : (size_pre >= cap)) (PreH2 : (size_pre <= INT_MAX)) (PreH3 : (cap >= 0)) (PreH4 : (cap <= INT_MAX)) (PreH5 : ((Zabs (old)) <= cap)) (PreH6 : (same_sign n old )) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  “ (size_pre >= cap) ” 
  &&  “ (size_pre <= INT_MAX) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign n old ) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_realloc_partial_solve_wit_2_pure := 
(
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap >= 0)) (PreH5 : (cap <= INT_MAX)) (PreH6 : ((Zabs (old)) <= cap)) (PreH7 : (same_sign n old )) (PreH8 : (cap <> 0)) ,
  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  “ (cap >= 0) ” 
  &&  “ (retval >= cap) ” 
  &&  “ ((Z.max (size_pre) (1)) >= cap) ”
) \/
(
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) (PreH1 : (old <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : (old >= INT_MIN)) (PreH5 : (retval >= INT_MIN)) (PreH6 : (retval = (Z.max (size_pre) (1)))) (PreH7 : (size_pre >= cap)) (PreH8 : (size_pre <= INT_MAX)) (PreH9 : (cap >= 0)) (PreH10 : (cap <= INT_MAX)) (PreH11 : ((Zabs (old)) <= cap)) (PreH12 : (same_sign n old )) (PreH13 : (cap <> 0)) ,
  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  “ ((Z.max (size_pre) (1)) >= cap) ” 
  &&  “ (retval >= cap) ”
).

Definition mpz_realloc_partial_solve_wit_2_pure_split_goal_1 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) (PreH1 : (old <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : (old >= INT_MIN)) (PreH5 : (retval >= INT_MIN)) (PreH6 : (retval = (Z.max (size_pre) (1)))) (PreH7 : (size_pre >= cap)) (PreH8 : (size_pre <= INT_MAX)) (PreH9 : (cap >= 0)) (PreH10 : (cap <= INT_MAX)) (PreH11 : ((Zabs (old)) <= cap)) (PreH12 : (same_sign n old )) (PreH13 : (cap <> 0)) ,
  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  “ ((Z.max (size_pre) (1)) >= cap) ”
.

Definition mpz_realloc_partial_solve_wit_2_pure_split_goal_2 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) (PreH1 : (old <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : (old >= INT_MIN)) (PreH5 : (retval >= INT_MIN)) (PreH6 : (retval = (Z.max (size_pre) (1)))) (PreH7 : (size_pre >= cap)) (PreH8 : (size_pre <= INT_MAX)) (PreH9 : (cap >= 0)) (PreH10 : (cap <= INT_MAX)) (PreH11 : ((Zabs (old)) <= cap)) (PreH12 : (same_sign n old )) (PreH13 : (cap <> 0)) ,
  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  “ (retval >= cap) ”
.

Definition mpz_realloc_partial_solve_wit_2_aux := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap >= 0)) (PreH5 : (cap <= INT_MAX)) (PreH6 : ((Zabs (old)) <= cap)) (PreH7 : (same_sign n old )) (PreH8 : (cap <> 0)) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  “ (cap >= 0) ” 
  &&  “ (retval >= cap) ” 
  &&  “ ((Z.max (size_pre) (1)) >= cap) ” 
  &&  “ (retval = (Z.max (size_pre) (1))) ” 
  &&  “ (size_pre >= cap) ” 
  &&  “ (size_pre <= INT_MAX) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign n old ) ” 
  &&  “ (cap <> 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_realloc_partial_solve_wit_2 := mpz_realloc_partial_solve_wit_2_pure -> mpz_realloc_partial_solve_wit_2_aux.

Definition mpz_realloc_partial_solve_wit_3_pure := 
(
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap >= 0)) (PreH5 : (cap <= INT_MAX)) (PreH6 : ((Zabs (old)) <= cap)) (PreH7 : (same_sign n old )) (PreH8 : (cap = 0)) ,
  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  “ (retval >= 0) ”
) \/
(
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) (PreH1 : (old <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : (old >= INT_MIN)) (PreH5 : (retval >= INT_MIN)) (PreH6 : (retval = (Z.max (size_pre) (1)))) (PreH7 : (size_pre >= cap)) (PreH8 : (size_pre <= INT_MAX)) (PreH9 : (cap >= 0)) (PreH10 : (cap <= INT_MAX)) (PreH11 : ((Zabs (old)) <= cap)) (PreH12 : (same_sign n old )) (PreH13 : (cap = 0)) ,
  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  “ (retval >= 0) ”
).

Definition mpz_realloc_partial_solve_wit_3_pure_split_goal_1 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) (PreH1 : (old <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : (old >= INT_MIN)) (PreH5 : (retval >= INT_MIN)) (PreH6 : (retval = (Z.max (size_pre) (1)))) (PreH7 : (size_pre >= cap)) (PreH8 : (size_pre <= INT_MAX)) (PreH9 : (cap >= 0)) (PreH10 : (cap <= INT_MAX)) (PreH11 : ((Zabs (old)) <= cap)) (PreH12 : (same_sign n old )) (PreH13 : (cap = 0)) ,
  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  “ (retval >= 0) ”
.

Definition mpz_realloc_partial_solve_wit_3_aux := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap >= 0)) (PreH5 : (cap <= INT_MAX)) (PreH6 : ((Zabs (old)) <= cap)) (PreH7 : (same_sign n old )) (PreH8 : (cap = 0)) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  “ (retval >= 0) ” 
  &&  “ (retval = (Z.max (size_pre) (1))) ” 
  &&  “ (size_pre >= cap) ” 
  &&  “ (size_pre <= INT_MAX) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign n old ) ” 
  &&  “ (cap = 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_realloc_partial_solve_wit_3 := mpz_realloc_partial_solve_wit_3_pure -> mpz_realloc_partial_solve_wit_3_aux.

Definition mpz_realloc_partial_solve_wit_4_pure := 
(
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap >= 0)) (PreH5 : (cap <= INT_MAX)) (PreH6 : ((Zabs (old)) <= cap)) (PreH7 : (same_sign n old )) (PreH8 : (cap <> 0)) ,
  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (old)) retval )
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  “ (old <= INT_MAX) ” 
  &&  “ (INT_MIN < old) ”
) \/
(
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (retval: Z) (retval_2: Z) (PreH1 : (old <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (old >= INT_MIN)) (PreH4 : (retval >= INT_MIN)) (PreH5 : (retval = (Z.max (size_pre) (1)))) (PreH6 : (size_pre >= cap)) (PreH7 : (size_pre <= INT_MAX)) (PreH8 : (cap >= 0)) (PreH9 : (cap <= INT_MAX)) (PreH10 : ((Zabs (old)) <= cap)) (PreH11 : (same_sign n old )) (PreH12 : (cap <> 0)) ,
  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (old)) retval )
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  “ (INT_MIN < old) ”
).

Definition mpz_realloc_partial_solve_wit_4_pure_split_goal_1 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (retval: Z) (retval_2: Z) (PreH1 : (old <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (old >= INT_MIN)) (PreH4 : (retval >= INT_MIN)) (PreH5 : (retval = (Z.max (size_pre) (1)))) (PreH6 : (size_pre >= cap)) (PreH7 : (size_pre <= INT_MAX)) (PreH8 : (cap >= 0)) (PreH9 : (cap <= INT_MAX)) (PreH10 : ((Zabs (old)) <= cap)) (PreH11 : (same_sign n old )) (PreH12 : (cap <> 0)) ,
  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (old)) retval )
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  “ (INT_MIN < old) ”
.

Definition mpz_realloc_partial_solve_wit_4_aux := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap >= 0)) (PreH5 : (cap <= INT_MAX)) (PreH6 : ((Zabs (old)) <= cap)) (PreH7 : (same_sign n old )) (PreH8 : (cap <> 0)) ,
  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (old)) retval )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  “ (old <= INT_MAX) ” 
  &&  “ (INT_MIN < old) ” 
  &&  “ (retval = (Z.max (size_pre) (1))) ” 
  &&  “ (size_pre >= cap) ” 
  &&  “ (size_pre <= INT_MAX) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign n old ) ” 
  &&  “ (cap <> 0) ”
  &&  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (old)) retval )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
.

Definition mpz_realloc_partial_solve_wit_4 := mpz_realloc_partial_solve_wit_4_pure -> mpz_realloc_partial_solve_wit_4_aux.

Definition mpz_realloc_partial_solve_wit_5_pure := 
(
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap >= 0)) (PreH5 : (cap <= INT_MAX)) (PreH6 : ((Zabs (old)) <= cap)) (PreH7 : (same_sign n old )) (PreH8 : (cap = 0)) ,
  (UIntArray.undef_full retval_2 retval )
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  “ (old <= INT_MAX) ” 
  &&  “ (INT_MIN < old) ”
) \/
(
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) (retval_2: Z) (PreH1 : (old <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (old >= INT_MIN)) (PreH4 : (retval >= INT_MIN)) (PreH5 : (retval = (Z.max (size_pre) (1)))) (PreH6 : (size_pre >= cap)) (PreH7 : (size_pre <= INT_MAX)) (PreH8 : (cap >= 0)) (PreH9 : (cap <= INT_MAX)) (PreH10 : ((Zabs (old)) <= cap)) (PreH11 : (same_sign n old )) (PreH12 : (cap = 0)) ,
  (UIntArray.undef_full retval_2 retval )
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  “ (INT_MIN < old) ”
).

Definition mpz_realloc_partial_solve_wit_5_pure_split_goal_1 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) (retval_2: Z) (PreH1 : (old <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (old >= INT_MIN)) (PreH4 : (retval >= INT_MIN)) (PreH5 : (retval = (Z.max (size_pre) (1)))) (PreH6 : (size_pre >= cap)) (PreH7 : (size_pre <= INT_MAX)) (PreH8 : (cap >= 0)) (PreH9 : (cap <= INT_MAX)) (PreH10 : ((Zabs (old)) <= cap)) (PreH11 : (same_sign n old )) (PreH12 : (cap = 0)) ,
  (UIntArray.undef_full retval_2 retval )
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  “ (INT_MIN < old) ”
.

Definition mpz_realloc_partial_solve_wit_5_aux := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval = (Z.max (size_pre) (1)))) (PreH2 : (size_pre >= cap)) (PreH3 : (size_pre <= INT_MAX)) (PreH4 : (cap >= 0)) (PreH5 : (cap <= INT_MAX)) (PreH6 : ((Zabs (old)) <= cap)) (PreH7 : (same_sign n old )) (PreH8 : (cap = 0)) ,
  (UIntArray.undef_full retval_2 retval )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  “ (old <= INT_MAX) ” 
  &&  “ (INT_MIN < old) ” 
  &&  “ (retval = (Z.max (size_pre) (1))) ” 
  &&  “ (size_pre >= cap) ” 
  &&  “ (size_pre <= INT_MAX) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign n old ) ” 
  &&  “ (cap = 0) ”
  &&  (UIntArray.undef_full retval_2 retval )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
.

Definition mpz_realloc_partial_solve_wit_5 := mpz_realloc_partial_solve_wit_5_pure -> mpz_realloc_partial_solve_wit_5_aux.

(*----- Function mrz_realloc_if -----*)

Definition mrz_realloc_if_return_wit_1 := 
(
forall (n_pre: Z) (z_pre: Z) (m: Z) (cap: Z) (old: Z) (ptr: Z) (PreH1 : (n_pre <= cap)) (PreH2 : (cap >= 0)) (PreH3 : (cap <= INT_MAX)) (PreH4 : (n_pre >= 1)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zabs (old)) <= cap)) (PreH7 : (same_sign m old )) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  EX (z_pre__mp_alloc: Z) ,
  “ (same_sign m old ) ” 
  &&  “ (z_pre__mp_alloc = (Z.max ((Z.max (n_pre) (1))) (cap))) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) (Z.max ((Z.max (n_pre) (1))) (cap)) )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_pre__mp_alloc)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
) \/
(
forall (n_pre: Z) (m: Z) (cap: Z) (old: Z) (ptr: Z) (PreH1 : (n_pre <= cap)) (PreH2 : (cap >= 0)) (PreH3 : (cap <= INT_MAX)) (PreH4 : (n_pre >= 1)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zabs (old)) <= cap)) (PreH7 : (same_sign m old )) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
|--
  “ (cap = (Z.max ((Z.max (n_pre) (1))) (cap))) ” 
  &&  “ (cap = (Z.max ((Z.max (n_pre) (1))) (cap))) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) (Z.max ((Z.max (n_pre) (1))) (cap)) )
).

Definition mrz_realloc_if_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (m: Z) (cap: Z) (old: Z) (ptr: Z) (PreH1 : (n_pre <= cap)) (PreH2 : (cap >= 0)) (PreH3 : (cap <= INT_MAX)) (PreH4 : (n_pre >= 1)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zabs (old)) <= cap)) (PreH7 : (same_sign m old )) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
|--
  “ (cap = (Z.max ((Z.max (n_pre) (1))) (cap))) ”
.

Definition mrz_realloc_if_return_wit_1_split_goal_2 := 
forall (n_pre: Z) (m: Z) (cap: Z) (old: Z) (ptr: Z) (PreH1 : (n_pre <= cap)) (PreH2 : (cap >= 0)) (PreH3 : (cap <= INT_MAX)) (PreH4 : (n_pre >= 1)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zabs (old)) <= cap)) (PreH7 : (same_sign m old )) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
|--
  “ (cap = (Z.max ((Z.max (n_pre) (1))) (cap))) ”
.

Definition mrz_realloc_if_return_wit_1_split_goal_spatial := 
forall (n_pre: Z) (m: Z) (cap: Z) (old: Z) (ptr: Z) (PreH1 : (n_pre <= cap)) (PreH2 : (cap >= 0)) (PreH3 : (cap <= INT_MAX)) (PreH4 : (n_pre >= 1)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zabs (old)) <= cap)) (PreH7 : (same_sign m old )) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
|--
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) (Z.max ((Z.max (n_pre) (1))) (cap)) )
.

Definition mrz_realloc_if_return_wit_2 := 
(
forall (n_pre: Z) (z_pre: Z) (m: Z) (cap: Z) (old: Z) (r_callee__mp_alloc: Z) (retval: Z) (PreH1 : (same_sign m old )) (PreH2 : (r_callee__mp_alloc = (Z.max (n_pre) (1)))) (PreH3 : (n_pre > cap)) (PreH4 : (cap >= 0)) (PreH5 : (cap <= INT_MAX)) (PreH6 : (n_pre >= 1)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : ((Zabs (old)) <= cap)) (PreH9 : (same_sign m old )) ,
  (mpd_store_Z_compact UINT_MOD retval (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval (Zabs (old)) (Z.max (n_pre) (1)) )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r_callee__mp_alloc)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
|--
  EX (z_pre__mp_alloc: Z) ,
  “ (same_sign m old ) ” 
  &&  “ (z_pre__mp_alloc = (Z.max ((Z.max (n_pre) (1))) (cap))) ”
  &&  (mpd_store_Z_compact UINT_MOD retval (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval (Zabs (old)) (Z.max ((Z.max (n_pre) (1))) (cap)) )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_pre__mp_alloc)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
) \/
(
forall (n_pre: Z) (m: Z) (cap: Z) (old: Z) (r_callee__mp_alloc: Z) (retval: Z) (PreH1 : (same_sign m old )) (PreH2 : (r_callee__mp_alloc = (Z.max (n_pre) (1)))) (PreH3 : (n_pre > cap)) (PreH4 : (cap >= 0)) (PreH5 : (cap <= INT_MAX)) (PreH6 : (n_pre >= 1)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : ((Zabs (old)) <= cap)) (PreH9 : (same_sign m old )) ,
  (mpd_store_Z_compact UINT_MOD retval (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval (Zabs (old)) (Z.max (n_pre) (1)) )
|--
  “ (r_callee__mp_alloc = (Z.max ((Z.max (n_pre) (1))) (cap))) ” 
  &&  “ (r_callee__mp_alloc = (Z.max ((Z.max (n_pre) (1))) (cap))) ”
  &&  (mpd_store_Z_compact UINT_MOD retval (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval (Zabs (old)) (Z.max ((Z.max (n_pre) (1))) (cap)) )
).

Definition mrz_realloc_if_return_wit_2_split_goal_1 := 
forall (n_pre: Z) (m: Z) (cap: Z) (old: Z) (r_callee__mp_alloc: Z) (retval: Z) (PreH1 : (same_sign m old )) (PreH2 : (r_callee__mp_alloc = (Z.max (n_pre) (1)))) (PreH3 : (n_pre > cap)) (PreH4 : (cap >= 0)) (PreH5 : (cap <= INT_MAX)) (PreH6 : (n_pre >= 1)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : ((Zabs (old)) <= cap)) (PreH9 : (same_sign m old )) ,
  (mpd_store_Z_compact UINT_MOD retval (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval (Zabs (old)) (Z.max (n_pre) (1)) )
|--
  “ (r_callee__mp_alloc = (Z.max ((Z.max (n_pre) (1))) (cap))) ”
.

Definition mrz_realloc_if_return_wit_2_split_goal_2 := 
forall (n_pre: Z) (m: Z) (cap: Z) (old: Z) (r_callee__mp_alloc: Z) (retval: Z) (PreH1 : (same_sign m old )) (PreH2 : (r_callee__mp_alloc = (Z.max (n_pre) (1)))) (PreH3 : (n_pre > cap)) (PreH4 : (cap >= 0)) (PreH5 : (cap <= INT_MAX)) (PreH6 : (n_pre >= 1)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : ((Zabs (old)) <= cap)) (PreH9 : (same_sign m old )) ,
  (mpd_store_Z_compact UINT_MOD retval (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval (Zabs (old)) (Z.max (n_pre) (1)) )
|--
  “ (r_callee__mp_alloc = (Z.max ((Z.max (n_pre) (1))) (cap))) ”
.

Definition mrz_realloc_if_return_wit_2_split_goal_spatial := 
forall (n_pre: Z) (m: Z) (cap: Z) (old: Z) (r_callee__mp_alloc: Z) (retval: Z) (PreH1 : (same_sign m old )) (PreH2 : (r_callee__mp_alloc = (Z.max (n_pre) (1)))) (PreH3 : (n_pre > cap)) (PreH4 : (cap >= 0)) (PreH5 : (cap <= INT_MAX)) (PreH6 : (n_pre >= 1)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : ((Zabs (old)) <= cap)) (PreH9 : (same_sign m old )) ,
  (mpd_store_Z_compact UINT_MOD retval (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval (Zabs (old)) (Z.max (n_pre) (1)) )
|--
  (mpd_store_Z_compact UINT_MOD retval (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg retval (Zabs (old)) (Z.max ((Z.max (n_pre) (1))) (cap)) )
.

Definition mrz_realloc_if_partial_solve_wit_1_pure := 
forall (n_pre: Z) (z_pre: Z) (m: Z) (cap: Z) (old: Z) (ptr: Z) (PreH1 : (n_pre > cap)) (PreH2 : (cap >= 0)) (PreH3 : (cap <= INT_MAX)) (PreH4 : (n_pre >= 1)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zabs (old)) <= cap)) (PreH7 : (same_sign m old )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Ptr  |-> z_pre)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  “ (n_pre >= cap) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign m old ) ”
.

Definition mrz_realloc_if_partial_solve_wit_1_aux := 
forall (n_pre: Z) (z_pre: Z) (m: Z) (cap: Z) (old: Z) (ptr: Z) (PreH1 : (n_pre > cap)) (PreH2 : (cap >= 0)) (PreH3 : (cap <= INT_MAX)) (PreH4 : (n_pre >= 1)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : ((Zabs (old)) <= cap)) (PreH7 : (same_sign m old )) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  “ (n_pre >= cap) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign m old ) ” 
  &&  “ (n_pre > cap) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (n_pre >= 1) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Zabs (old)) <= cap) ” 
  &&  “ (same_sign m old ) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m)) (Zabs (old)) )
  **  (UIntArray.undef_seg ptr (Zabs (old)) cap )
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((z_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mrz_realloc_if_partial_solve_wit_1 := mrz_realloc_if_partial_solve_wit_1_pure -> mrz_realloc_if_partial_solve_wit_1_aux.

(*----- Function mpz_sgn -----*)

Definition mpz_sgn_safety_wit_1 := 
forall (u_pre: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign n size )) (PreH2 : ((Zabs (size)) <= cap)) ,
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
forall (u_pre: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (size < 0)) (PreH2 : (retval = (-1))) (PreH3 : (same_sign n size )) (PreH4 : ((Zabs (size)) <= cap)) ,
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
forall (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (size < 0)) (PreH2 : (retval = (-1))) (PreH3 : (same_sign n size )) (PreH4 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
|--
  “ (n < 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
).

Definition mpz_sgn_return_wit_1_split_goal_1 := 
forall (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (size < 0)) (PreH2 : (retval = (-1))) (PreH3 : (same_sign n size )) (PreH4 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
|--
  “ (n < 0) ”
.

Definition mpz_sgn_return_wit_1_split_goal_spatial := 
forall (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (size < 0)) (PreH2 : (retval = (-1))) (PreH3 : (same_sign n size )) (PreH4 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
|--
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
.

Definition mpz_sgn_return_wit_2 := 
(
forall (u_pre: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (size = 0)) (PreH2 : (retval = 0)) (PreH3 : (same_sign n size )) (PreH4 : ((Zabs (size)) <= cap)) ,
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
forall (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (size = 0)) (PreH2 : (retval = 0)) (PreH3 : (same_sign n size )) (PreH4 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
|--
  “ (n = 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
).

Definition mpz_sgn_return_wit_2_split_goal_1 := 
forall (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (size = 0)) (PreH2 : (retval = 0)) (PreH3 : (same_sign n size )) (PreH4 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
|--
  “ (n = 0) ”
.

Definition mpz_sgn_return_wit_2_split_goal_spatial := 
forall (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (size = 0)) (PreH2 : (retval = 0)) (PreH3 : (same_sign n size )) (PreH4 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
|--
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
.

Definition mpz_sgn_return_wit_3 := 
(
forall (u_pre: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (size > 0)) (PreH2 : (retval = 1)) (PreH3 : (same_sign n size )) (PreH4 : ((Zabs (size)) <= cap)) ,
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
forall (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (size > 0)) (PreH2 : (retval = 1)) (PreH3 : (same_sign n size )) (PreH4 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
|--
  “ (n > 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
).

Definition mpz_sgn_return_wit_3_split_goal_1 := 
forall (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (size > 0)) (PreH2 : (retval = 1)) (PreH3 : (same_sign n size )) (PreH4 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
|--
  “ (n > 0) ”
.

Definition mpz_sgn_return_wit_3_split_goal_spatial := 
forall (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (size > 0)) (PreH2 : (retval = 1)) (PreH3 : (same_sign n size )) (PreH4 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
|--
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
.

Definition mpz_sgn_partial_solve_wit_1 := 
forall (u_pre: Z) (n: Z) ,
  (store_Z u_pre n )
|--
  EX (cap: Z)  (size: Z)  (ptr: Z) ,
  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
.

Definition mpz_sgn_partial_solve_wit_2 := 
forall (u_pre: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign n size )) (PreH2 : ((Zabs (size)) <= cap)) ,
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

(*----- Function mpz_swap -----*)

Definition mpz_swap_return_wit_1 := 
forall (v_pre: Z) (u_pre: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign m size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign n size )) (PreH4 : ((Zabs (size)) <= cap)) ,
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
|--
  (store_Z u_pre m )
  **  (store_Z v_pre n )
.

Definition mpz_swap_partial_solve_wit_1 := 
forall (v_pre: Z) (u_pre: Z) (m: Z) (n: Z) ,
  (store_Z u_pre n )
  **  (store_Z v_pre m )
|--
  EX (cap_2: Z)  (size_2: Z)  (ptr_2: Z)  (cap: Z)  (size: Z)  (ptr: Z) ,
  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
.

Definition mpz_swap_partial_solve_wit_2 := 
forall (v_pre: Z) (u_pre: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign m size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign n size )) (PreH4 : ((Zabs (size)) <= cap)) ,
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
|--
  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
.

Definition mpz_swap_partial_solve_wit_3 := 
forall (v_pre: Z) (u_pre: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign m size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign n size )) (PreH4 : ((Zabs (size)) <= cap)) ,
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
|--
  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
.

(*----- Function mpz_abs_add -----*)

Definition mpz_abs_add_safety_wit_1 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (n_new: Z) (m_new: Z) (aptr: Z) (bptr: Z) (asize: Z) (bsize: Z) (acap: Z) (bcap: Z) (rptr: Z) (rsize: Z) (rcap: Z) (b: Z) (a: Z) (an: Z) (bn: Z) (PreH1 : (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) ((@nil (Z * Z)))))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) ((@nil (Z * Z)))))) )) (PreH2 : (an >= bn)) (PreH3 : (an = (Zabs (asize)))) (PreH4 : (bn = (Zabs (bsize)))) (PreH5 : (an <= acap)) (PreH6 : (bn <= bcap)) (PreH7 : (same_sign n_new asize )) (PreH8 : (same_sign m_new bsize )) (PreH9 : ((Zabs (rsize)) <= rcap)) (PreH10 : (same_sign l rsize )) (PreH11 : (rcap >= 0)) ,
  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (m_new)) bn )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
|--
  “ ((an + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (an + 1 )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (n_new: Z) (m_new: Z) (aptr: Z) (bptr: Z) (asize: Z) (bsize: Z) (acap: Z) (bcap: Z) (rptr: Z) (rsize: Z) (rcap: Z) (b: Z) (a: Z) (an: Z) (bn: Z) (PreH1 : (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) ((@nil (Z * Z)))))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) ((@nil (Z * Z)))))) )) (PreH2 : (an >= bn)) (PreH3 : (an = (Zabs (asize)))) (PreH4 : (bn = (Zabs (bsize)))) (PreH5 : (an <= acap)) (PreH6 : (bn <= bcap)) (PreH7 : (same_sign n_new asize )) (PreH8 : (same_sign m_new bsize )) (PreH9 : ((Zabs (rsize)) <= rcap)) (PreH10 : (same_sign l rsize )) (PreH11 : (rcap >= 0)) ,
  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (m_new)) bn )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
|--
  “ ((an + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (an + 1 )) ”
).

Definition mpz_abs_add_safety_wit_1_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (n_new: Z) (m_new: Z) (aptr: Z) (bptr: Z) (asize: Z) (bsize: Z) (acap: Z) (bcap: Z) (rptr: Z) (rsize: Z) (rcap: Z) (b: Z) (a: Z) (an: Z) (bn: Z) (PreH1 : (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) ((@nil (Z * Z)))))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) ((@nil (Z * Z)))))) )) (PreH2 : (an >= bn)) (PreH3 : (an = (Zabs (asize)))) (PreH4 : (bn = (Zabs (bsize)))) (PreH5 : (an <= acap)) (PreH6 : (bn <= bcap)) (PreH7 : (same_sign n_new asize )) (PreH8 : (same_sign m_new bsize )) (PreH9 : ((Zabs (rsize)) <= rcap)) (PreH10 : (same_sign l rsize )) (PreH11 : (rcap >= 0)) ,
  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (m_new)) bn )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
|--
  “ ((an + 1 ) <= INT_MAX) ”
.

Definition mpz_abs_add_safety_wit_1_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (n_new: Z) (m_new: Z) (aptr: Z) (bptr: Z) (asize: Z) (bsize: Z) (acap: Z) (bcap: Z) (rptr: Z) (rsize: Z) (rcap: Z) (b: Z) (a: Z) (an: Z) (bn: Z) (PreH1 : (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) ((@nil (Z * Z)))))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) ((@nil (Z * Z)))))) )) (PreH2 : (an >= bn)) (PreH3 : (an = (Zabs (asize)))) (PreH4 : (bn = (Zabs (bsize)))) (PreH5 : (an <= acap)) (PreH6 : (bn <= bcap)) (PreH7 : (same_sign n_new asize )) (PreH8 : (same_sign m_new bsize )) (PreH9 : ((Zabs (rsize)) <= rcap)) (PreH10 : (same_sign l rsize )) (PreH11 : (rcap >= 0)) ,
  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (m_new)) bn )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
|--
  “ ((INT_MIN) <= (an + 1 )) ”
.

Definition mpz_abs_add_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (n_new: Z) (m_new: Z) (aptr: Z) (bptr: Z) (asize: Z) (bsize: Z) (acap: Z) (bcap: Z) (rptr: Z) (rsize: Z) (rcap: Z) (b: Z) (a: Z) (an: Z) (bn: Z) (PreH1 : (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) ((@nil (Z * Z)))))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) ((@nil (Z * Z)))))) )) (PreH2 : (an >= bn)) (PreH3 : (an = (Zabs (asize)))) (PreH4 : (bn = (Zabs (bsize)))) (PreH5 : (an <= acap)) (PreH6 : (bn <= bcap)) (PreH7 : (same_sign n_new asize )) (PreH8 : (same_sign m_new bsize )) (PreH9 : ((Zabs (rsize)) <= rcap)) (PreH10 : (same_sign l rsize )) (PreH11 : (rcap >= 0)) ,
  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (m_new)) bn )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpz_abs_add_entail_wit_1_1 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (PreH1 : (retval >= retval_2)) (PreH2 : (retval_2 = (Zabs (size_2)))) (PreH3 : (same_sign m size_2 )) (PreH4 : ((Zabs (size_2)) <= cap_2)) (PreH5 : (retval = (Zabs (size)))) (PreH6 : (same_sign n size )) (PreH7 : ((Zabs (size)) <= cap)) ,
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
|--
  EX (rptr: Z)  (bptr: Z)  (aptr: Z)  (rcap: Z)  (rsize: Z)  (bcap: Z)  (acap: Z)  (bsize: Z)  (asize: Z)  (n_new: Z)  (m_new: Z) ,
  “ (Permutation (cons ((Prod2 (a_pre) (n_new))) ((cons ((Prod2 (b_pre) (m_new))) ((@nil (Z * Z)))))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) ((@nil (Z * Z)))))) ) ” 
  &&  “ (retval >= retval_2) ” 
  &&  “ (retval = (Zabs (asize))) ” 
  &&  “ (retval_2 = (Zabs (bsize))) ” 
  &&  “ (retval <= acap) ” 
  &&  “ (retval_2 <= bcap) ” 
  &&  “ (same_sign n_new asize ) ” 
  &&  “ (same_sign m_new bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ (rcap >= 0) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg aptr retval acap )
  **  (UIntArray.undef_seg bptr retval_2 bcap )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (n_new)) retval )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (m_new)) retval_2 )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
) \/
(
forall (b_pre: Z) (a_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (ptr_3: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign l size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : (retval >= retval_2)) (PreH4 : (retval_2 = (Zabs (size_2)))) (PreH5 : (same_sign m size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (retval = (Zabs (size)))) (PreH8 : (same_sign n size )) (PreH9 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs (l)) (Zabs (size_3)) )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
|--
  EX (n_new: Z)  (m_new: Z) ,
  “ (Permutation (cons ((Prod2 (a_pre) (n_new))) ((cons ((Prod2 (b_pre) (m_new))) ((@nil (Z * Z)))))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) ((@nil (Z * Z)))))) ) ” 
  &&  “ (retval >= retval_2) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (retval_2 = (Zabs (size_2))) ” 
  &&  “ (retval <= cap) ” 
  &&  “ (retval_2 <= cap_2) ” 
  &&  “ (same_sign n_new size ) ” 
  &&  “ (same_sign m_new size_2 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ (same_sign l size_3 ) ” 
  &&  “ (cap_3 >= 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n_new)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m_new)) retval_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs (l)) (Zabs (size_3)) )
).

Definition mpz_abs_add_entail_wit_1_2 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (PreH1 : (retval < retval_2)) (PreH2 : (retval_2 = (Zabs (size_2)))) (PreH3 : (same_sign m size_2 )) (PreH4 : ((Zabs (size_2)) <= cap_2)) (PreH5 : (retval = (Zabs (size)))) (PreH6 : (same_sign n size )) (PreH7 : ((Zabs (size)) <= cap)) ,
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
|--
  EX (rptr: Z)  (bptr: Z)  (aptr: Z)  (rcap: Z)  (rsize: Z)  (bcap: Z)  (acap: Z)  (bsize: Z)  (asize: Z)  (n_new: Z)  (m_new: Z) ,
  “ (Permutation (cons ((Prod2 (b_pre) (n_new))) ((cons ((Prod2 (a_pre) (m_new))) ((@nil (Z * Z)))))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) ((@nil (Z * Z)))))) ) ” 
  &&  “ (retval_2 >= retval) ” 
  &&  “ (retval_2 = (Zabs (asize))) ” 
  &&  “ (retval = (Zabs (bsize))) ” 
  &&  “ (retval_2 <= acap) ” 
  &&  “ (retval <= bcap) ” 
  &&  “ (same_sign n_new asize ) ” 
  &&  “ (same_sign m_new bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ (rcap >= 0) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg aptr retval_2 acap )
  **  (UIntArray.undef_seg bptr retval bcap )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (n_new)) retval_2 )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (m_new)) retval )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
) \/
(
forall (b_pre: Z) (a_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (ptr_3: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign l size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : (retval < retval_2)) (PreH4 : (retval_2 = (Zabs (size_2)))) (PreH5 : (same_sign m size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (retval = (Zabs (size)))) (PreH8 : (same_sign n size )) (PreH9 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs (l)) (Zabs (size_3)) )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
|--
  EX (n_new: Z)  (m_new: Z) ,
  “ (Permutation (cons ((Prod2 (b_pre) (n_new))) ((cons ((Prod2 (a_pre) (m_new))) ((@nil (Z * Z)))))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) ((@nil (Z * Z)))))) ) ” 
  &&  “ (retval_2 >= retval) ” 
  &&  “ (retval_2 = (Zabs (size_2))) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (retval_2 <= cap_2) ” 
  &&  “ (retval <= cap) ” 
  &&  “ (same_sign n_new size_2 ) ” 
  &&  “ (same_sign m_new size ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ (same_sign l size_3 ) ” 
  &&  “ (cap_3 >= 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (n_new)) retval_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (m_new)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs (l)) (Zabs (size_3)) )
).

Definition mpz_abs_add_entail_wit_2 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (n_new_2: Z) (m_new_2: Z) (aptr_2: Z) (bptr_2: Z) (asize_2: Z) (bsize_2: Z) (acap_2: Z) (bcap_2: Z) (rsize_2: Z) (rcap_2: Z) (b: Z) (a: Z) (an: Z) (bn: Z) (z_callee__mp_alloc: Z) (retval: Z) (PreH1 : (same_sign l rsize_2 )) (PreH2 : (z_callee__mp_alloc = (Z.max ((Z.max ((an + 1 )) (1))) (rcap_2)))) (PreH3 : (Permutation (cons ((Prod2 (a) (n_new_2))) ((cons ((Prod2 (b) (m_new_2))) ((@nil (Z * Z)))))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) ((@nil (Z * Z)))))) )) (PreH4 : (an >= bn)) (PreH5 : (an = (Zabs (asize_2)))) (PreH6 : (bn = (Zabs (bsize_2)))) (PreH7 : (an <= acap_2)) (PreH8 : (bn <= bcap_2)) (PreH9 : (same_sign n_new_2 asize_2 )) (PreH10 : (same_sign m_new_2 bsize_2 )) (PreH11 : ((Zabs (rsize_2)) <= rcap_2)) (PreH12 : (same_sign l rsize_2 )) (PreH13 : (rcap_2 >= 0)) ,
  (mpd_store_Z_compact UINT_MOD retval (Zabs (l)) (Zabs (rsize_2)) )
  **  (UIntArray.undef_seg retval (Zabs (rsize_2)) (Z.max ((Z.max ((an + 1 )) (1))) (rcap_2)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_callee__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr_2)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize_2)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap_2)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr_2)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize_2)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap_2)
  **  (UIntArray.undef_seg aptr_2 an acap_2 )
  **  (UIntArray.undef_seg bptr_2 bn bcap_2 )
  **  (mpd_store_Z_compact UINT_MOD aptr_2 (Zabs (n_new_2)) an )
  **  (mpd_store_Z_compact UINT_MOD bptr_2 (Zabs (m_new_2)) bn )
|--
  EX (bptr: Z)  (aptr: Z)  (r__mp_d: Z)  (r__mp_alloc: Z)  (rcap: Z)  (rsize: Z)  (bcap: Z)  (acap: Z)  (bsize: Z)  (asize: Z)  (n_new: Z)  (m_new: Z) ,
  “ (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) ((@nil (Z * Z)))))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) ((@nil (Z * Z)))))) ) ” 
  &&  “ (an >= bn) ” 
  &&  “ (an = (Zabs (asize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (an <= acap) ” 
  &&  “ (bn <= bcap) ” 
  &&  “ (same_sign n_new asize ) ” 
  &&  “ (same_sign m_new bsize ) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (r__mp_alloc = (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ” 
  &&  “ (r__mp_d = retval) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) ) ” 
  &&  “ (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (m_new)) bn )
  **  (UIntArray.undef_full retval an )
  **  (UIntArray.undef_seg retval an (Z.max ((Z.max ((an + 1 )) (1))) (rcap)) )
) \/
(
forall (b_pre: Z) (a_pre: Z) (l: Z) (m: Z) (n: Z) (n_new_2: Z) (m_new_2: Z) (aptr_2: Z) (bptr_2: Z) (asize_2: Z) (bsize_2: Z) (acap_2: Z) (bcap_2: Z) (rsize_2: Z) (rcap_2: Z) (b: Z) (a: Z) (an: Z) (bn: Z) (z_callee__mp_alloc: Z) (retval: Z) (PreH1 : (same_sign l rsize_2 )) (PreH2 : (z_callee__mp_alloc = (Z.max ((Z.max ((an + 1 )) (1))) (rcap_2)))) (PreH3 : (Permutation (cons ((Prod2 (a) (n_new_2))) ((cons ((Prod2 (b) (m_new_2))) ((@nil (Z * Z)))))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) ((@nil (Z * Z)))))) )) (PreH4 : (an >= bn)) (PreH5 : (an = (Zabs (asize_2)))) (PreH6 : (bn = (Zabs (bsize_2)))) (PreH7 : (an <= acap_2)) (PreH8 : (bn <= bcap_2)) (PreH9 : (same_sign n_new_2 asize_2 )) (PreH10 : (same_sign m_new_2 bsize_2 )) (PreH11 : ((Zabs (rsize_2)) <= rcap_2)) (PreH12 : (same_sign l rsize_2 )) (PreH13 : (rcap_2 >= 0)) ,
  (mpd_store_Z_compact UINT_MOD retval (Zabs (l)) (Zabs (rsize_2)) )
  **  (UIntArray.undef_seg retval (Zabs (rsize_2)) (Z.max ((Z.max ((an + 1 )) (1))) (rcap_2)) )
  **  (mpd_store_Z_compact UINT_MOD aptr_2 (Zabs (n_new_2)) an )
  **  (mpd_store_Z_compact UINT_MOD bptr_2 (Zabs (m_new_2)) bn )
|--
  EX (rcap: Z)  (n_new: Z)  (m_new: Z) ,
  “ (z_callee__mp_alloc = (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ” 
  &&  “ (z_callee__mp_alloc = (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ” 
  &&  “ (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) ((@nil (Z * Z)))))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) ((@nil (Z * Z)))))) ) ” 
  &&  “ (an >= bn) ” 
  &&  “ (an = (Zabs (asize_2))) ” 
  &&  “ (bn = (Zabs (bsize_2))) ” 
  &&  “ (an <= acap_2) ” 
  &&  “ (bn <= bcap_2) ” 
  &&  “ (same_sign n_new asize_2 ) ” 
  &&  “ (same_sign m_new bsize_2 ) ” 
  &&  “ (same_sign l rsize_2 ) ” 
  &&  “ ((Zabs (rsize_2)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize_2)) ) ” 
  &&  “ (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ”
  &&  (mpd_store_Z_compact UINT_MOD aptr_2 (Zabs (n_new)) an )
  **  (mpd_store_Z_compact UINT_MOD bptr_2 (Zabs (m_new)) bn )
  **  (UIntArray.undef_full retval an )
  **  (UIntArray.undef_seg retval an (Z.max ((Z.max ((an + 1 )) (1))) (rcap)) )
).

Definition mpz_abs_add_return_wit_1 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (n_new: Z) (m_new: Z) (aptr: Z) (bptr: Z) (asize: Z) (bsize: Z) (acap: Z) (bcap: Z) (rsize: Z) (rcap: Z) (b: Z) (a: Z) (an: Z) (bn: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (val_r_out: Z) (retval: Z) (PreH1 : ((val_r_out + (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (n_new)) + (Zabs (m_new)) ))) (PreH2 : (is_compact_Z UINT_MOD (Zabs (m_new)) bn )) (PreH3 : (is_compact_Z UINT_MOD (Zabs (n_new)) an )) (PreH4 : (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) ((@nil (Z * Z)))))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) ((@nil (Z * Z)))))) )) (PreH5 : (an >= bn)) (PreH6 : (an = (Zabs (asize)))) (PreH7 : (bn = (Zabs (bsize)))) (PreH8 : (an <= acap)) (PreH9 : (bn <= bcap)) (PreH10 : (same_sign n_new asize )) (PreH11 : (same_sign m_new bsize )) (PreH12 : (same_sign l rsize )) (PreH13 : ((Zabs (rsize)) <= rcap)) (PreH14 : (rcap >= 0)) (PreH15 : (r__mp_alloc = (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) (PreH16 : (r__mp_d = rp)) (PreH17 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH18 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) ,
  (((rp + (an * sizeof(UINT)))) # UInt  |-> retval)
  **  (UIntArray.undef_seg rp (an + 1 ) (Z.max ((Z.max ((an + 1 )) (1))) (rcap)) )
  **  (mpd_store_Z UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z UINT_MOD bptr (Zabs (m_new)) bn )
  **  (mpd_store_Z UINT_MOD rp val_r_out an )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) + (Zabs (m)) ) (signed_last_nbits (((unsigned_last_nbits (an) (32)) + retval )) (32)) )
) \/
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (n_new: Z) (m_new: Z) (aptr: Z) (bptr: Z) (asize: Z) (bsize: Z) (acap: Z) (bcap: Z) (rsize: Z) (rcap: Z) (b: Z) (a: Z) (an: Z) (bn: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (val_r_out: Z) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (bcap <= INT_MAX)) (PreH4 : (bsize <= INT_MAX)) (PreH5 : (acap <= INT_MAX)) (PreH6 : (asize <= INT_MAX)) (PreH7 : (r__mp_alloc <= INT_MAX)) (PreH8 : (rsize <= INT_MAX)) (PreH9 : (bcap >= INT_MIN)) (PreH10 : (bsize >= INT_MIN)) (PreH11 : (acap >= INT_MIN)) (PreH12 : (asize >= INT_MIN)) (PreH13 : (r__mp_alloc >= INT_MIN)) (PreH14 : (rsize >= INT_MIN)) (PreH15 : ((val_r_out + (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (n_new)) + (Zabs (m_new)) ))) (PreH16 : (is_compact_Z UINT_MOD (Zabs (m_new)) bn )) (PreH17 : (is_compact_Z UINT_MOD (Zabs (n_new)) an )) (PreH18 : (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) ((@nil (Z * Z)))))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) ((@nil (Z * Z)))))) )) (PreH19 : (an >= bn)) (PreH20 : (an = (Zabs (asize)))) (PreH21 : (bn = (Zabs (bsize)))) (PreH22 : (an <= acap)) (PreH23 : (bn <= bcap)) (PreH24 : (same_sign n_new asize )) (PreH25 : (same_sign m_new bsize )) (PreH26 : (same_sign l rsize )) (PreH27 : ((Zabs (rsize)) <= rcap)) (PreH28 : (rcap >= 0)) (PreH29 : (r__mp_alloc = (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) (PreH30 : (r__mp_d = rp)) (PreH31 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH32 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) ,
  (((rp + (an * sizeof(UINT)))) # UInt  |-> retval)
  **  (UIntArray.undef_seg rp (an + 1 ) (Z.max ((Z.max ((an + 1 )) (1))) (rcap)) )
  **  (mpd_store_Z UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z UINT_MOD bptr (Zabs (m_new)) bn )
  **  (mpd_store_Z UINT_MOD rp val_r_out an )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) + (Zabs (m)) ) (signed_last_nbits (((unsigned_last_nbits (an) (32)) + retval )) (32)) )
).

Definition mpz_abs_add_return_wit_1_split_goal_spatial := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (n_new: Z) (m_new: Z) (aptr: Z) (bptr: Z) (asize: Z) (bsize: Z) (acap: Z) (bcap: Z) (rsize: Z) (rcap: Z) (b: Z) (a: Z) (an: Z) (bn: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (val_r_out: Z) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (bcap <= INT_MAX)) (PreH4 : (bsize <= INT_MAX)) (PreH5 : (acap <= INT_MAX)) (PreH6 : (asize <= INT_MAX)) (PreH7 : (r__mp_alloc <= INT_MAX)) (PreH8 : (rsize <= INT_MAX)) (PreH9 : (bcap >= INT_MIN)) (PreH10 : (bsize >= INT_MIN)) (PreH11 : (acap >= INT_MIN)) (PreH12 : (asize >= INT_MIN)) (PreH13 : (r__mp_alloc >= INT_MIN)) (PreH14 : (rsize >= INT_MIN)) (PreH15 : ((val_r_out + (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (n_new)) + (Zabs (m_new)) ))) (PreH16 : (is_compact_Z UINT_MOD (Zabs (m_new)) bn )) (PreH17 : (is_compact_Z UINT_MOD (Zabs (n_new)) an )) (PreH18 : (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) ((@nil (Z * Z)))))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) ((@nil (Z * Z)))))) )) (PreH19 : (an >= bn)) (PreH20 : (an = (Zabs (asize)))) (PreH21 : (bn = (Zabs (bsize)))) (PreH22 : (an <= acap)) (PreH23 : (bn <= bcap)) (PreH24 : (same_sign n_new asize )) (PreH25 : (same_sign m_new bsize )) (PreH26 : (same_sign l rsize )) (PreH27 : ((Zabs (rsize)) <= rcap)) (PreH28 : (rcap >= 0)) (PreH29 : (r__mp_alloc = (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) (PreH30 : (r__mp_d = rp)) (PreH31 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH32 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) ,
  (((rp + (an * sizeof(UINT)))) # UInt  |-> retval)
  **  (UIntArray.undef_seg rp (an + 1 ) (Z.max ((Z.max ((an + 1 )) (1))) (rcap)) )
  **  (mpd_store_Z UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z UINT_MOD bptr (Zabs (m_new)) bn )
  **  (mpd_store_Z UINT_MOD rp val_r_out an )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
|--
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) + (Zabs (m)) ) (signed_last_nbits (((unsigned_last_nbits (an) (32)) + retval )) (32)) )
.

Definition mpz_abs_add_partial_solve_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) ,
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
|--
  EX (cap: Z)  (size: Z)  (ptr: Z) ,
  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
.

Definition mpz_abs_add_partial_solve_wit_2_pure := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign n size )) (PreH2 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
|--
  “ (size <= INT_MAX) ” 
  &&  “ (INT_MIN < size) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (cap <= INT_MAX)) (PreH2 : (size <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : (size >= INT_MIN)) (PreH5 : (same_sign n size )) (PreH6 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
|--
  “ (INT_MIN < size) ”
).

Definition mpz_abs_add_partial_solve_wit_2_pure_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (cap <= INT_MAX)) (PreH2 : (size <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : (size >= INT_MIN)) (PreH5 : (same_sign n size )) (PreH6 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
|--
  “ (INT_MIN < size) ”
.

Definition mpz_abs_add_partial_solve_wit_2_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign n size )) (PreH2 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
|--
  “ (size <= INT_MAX) ” 
  &&  “ (INT_MIN < size) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
.

Definition mpz_abs_add_partial_solve_wit_2 := mpz_abs_add_partial_solve_wit_2_pure -> mpz_abs_add_partial_solve_wit_2_aux.

Definition mpz_abs_add_partial_solve_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval = (Zabs (size)))) (PreH2 : (same_sign n size )) (PreH3 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
|--
  EX (cap_2: Z)  (size_2: Z)  (ptr_2: Z) ,
  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
.

Definition mpz_abs_add_partial_solve_wit_4_pure := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size_2: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size: Z) (cap_2: Z) (PreH1 : (same_sign m size )) (PreH2 : ((Zabs (size)) <= cap_2)) (PreH3 : (retval = (Zabs (size_2)))) (PreH4 : (same_sign n size_2 )) (PreH5 : ((Zabs (size_2)) <= cap)) ,
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |->_)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_2)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ (size <= INT_MAX) ” 
  &&  “ (INT_MIN < size) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size_2: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size: Z) (cap_2: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (cap <= INT_MAX)) (PreH3 : (size_2 <= INT_MAX)) (PreH4 : (cap_2 <= INT_MAX)) (PreH5 : (size <= INT_MAX)) (PreH6 : (retval >= INT_MIN)) (PreH7 : (cap >= INT_MIN)) (PreH8 : (size_2 >= INT_MIN)) (PreH9 : (cap_2 >= INT_MIN)) (PreH10 : (size >= INT_MIN)) (PreH11 : (same_sign m size )) (PreH12 : ((Zabs (size)) <= cap_2)) (PreH13 : (retval = (Zabs (size_2)))) (PreH14 : (same_sign n size_2 )) (PreH15 : ((Zabs (size_2)) <= cap)) ,
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |->_)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_2)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ (INT_MIN < size) ”
).

Definition mpz_abs_add_partial_solve_wit_4_pure_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size_2: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size: Z) (cap_2: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (cap <= INT_MAX)) (PreH3 : (size_2 <= INT_MAX)) (PreH4 : (cap_2 <= INT_MAX)) (PreH5 : (size <= INT_MAX)) (PreH6 : (retval >= INT_MIN)) (PreH7 : (cap >= INT_MIN)) (PreH8 : (size_2 >= INT_MIN)) (PreH9 : (cap_2 >= INT_MIN)) (PreH10 : (size >= INT_MIN)) (PreH11 : (same_sign m size )) (PreH12 : ((Zabs (size)) <= cap_2)) (PreH13 : (retval = (Zabs (size_2)))) (PreH14 : (same_sign n size_2 )) (PreH15 : ((Zabs (size_2)) <= cap)) ,
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |->_)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_2)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ (INT_MIN < size) ”
.

Definition mpz_abs_add_partial_solve_wit_4_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size_2: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size: Z) (cap_2: Z) (PreH1 : (same_sign m size )) (PreH2 : ((Zabs (size)) <= cap_2)) (PreH3 : (retval = (Zabs (size_2)))) (PreH4 : (same_sign n size_2 )) (PreH5 : ((Zabs (size_2)) <= cap)) ,
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_2)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
|--
  “ (size <= INT_MAX) ” 
  &&  “ (INT_MIN < size) ” 
  &&  “ (same_sign m size ) ” 
  &&  “ ((Zabs (size)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size_2))) ” 
  &&  “ (same_sign n size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_2)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
.

Definition mpz_abs_add_partial_solve_wit_4 := mpz_abs_add_partial_solve_wit_4_pure -> mpz_abs_add_partial_solve_wit_4_aux.

Definition mpz_abs_add_partial_solve_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (PreH1 : (retval < retval_2)) (PreH2 : (retval_2 = (Zabs (size_2)))) (PreH3 : (same_sign m size_2 )) (PreH4 : ((Zabs (size_2)) <= cap_2)) (PreH5 : (retval = (Zabs (size)))) (PreH6 : (same_sign n size )) (PreH7 : ((Zabs (size)) <= cap)) ,
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
|--
  “ (retval < retval_2) ” 
  &&  “ (retval_2 = (Zabs (size_2))) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
.

Definition mpz_abs_add_partial_solve_wit_6 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (PreH1 : (retval < retval_2)) (PreH2 : (retval_2 = (Zabs (size_2)))) (PreH3 : (same_sign m size_2 )) (PreH4 : ((Zabs (size_2)) <= cap_2)) (PreH5 : (retval = (Zabs (size)))) (PreH6 : (same_sign n size )) (PreH7 : ((Zabs (size)) <= cap)) ,
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
|--
  “ (retval < retval_2) ” 
  &&  “ (retval_2 = (Zabs (size_2))) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
.

Definition mpz_abs_add_partial_solve_wit_7_pure := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (n_new: Z) (m_new: Z) (aptr: Z) (bptr: Z) (asize: Z) (bsize: Z) (acap: Z) (bcap: Z) (rptr: Z) (rsize: Z) (rcap: Z) (b: Z) (a: Z) (an: Z) (bn: Z) (PreH1 : (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) ((@nil (Z * Z)))))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) ((@nil (Z * Z)))))) )) (PreH2 : (an >= bn)) (PreH3 : (an = (Zabs (asize)))) (PreH4 : (bn = (Zabs (bsize)))) (PreH5 : (an <= acap)) (PreH6 : (bn <= bcap)) (PreH7 : (same_sign n_new asize )) (PreH8 : (same_sign m_new bsize )) (PreH9 : ((Zabs (rsize)) <= rcap)) (PreH10 : (same_sign l rsize )) (PreH11 : (rcap >= 0)) ,
  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (m_new)) bn )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
|--
  “ (rcap >= 0) ” 
  &&  “ ((an + 1 ) >= 1) ” 
  &&  “ ((an + 1 ) <= INT_MAX) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ (((Zabs (asize)) + 1 ) <= INT_MAX) ” 
  &&  “ (((Zabs (asize)) + 1 ) >= 1) ” 
  &&  “ (rcap <= INT_MAX) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (n_new: Z) (m_new: Z) (aptr: Z) (bptr: Z) (asize: Z) (bsize: Z) (acap: Z) (bcap: Z) (rptr: Z) (rsize: Z) (rcap: Z) (b: Z) (a: Z) (an: Z) (bn: Z) (PreH1 : (rcap <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (bcap <= INT_MAX)) (PreH4 : (bsize <= INT_MAX)) (PreH5 : (acap <= INT_MAX)) (PreH6 : (asize <= INT_MAX)) (PreH7 : (bn <= INT_MAX)) (PreH8 : (an <= INT_MAX)) (PreH9 : (rcap >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bcap >= INT_MIN)) (PreH12 : (bsize >= INT_MIN)) (PreH13 : (acap >= INT_MIN)) (PreH14 : (asize >= INT_MIN)) (PreH15 : (bn >= INT_MIN)) (PreH16 : (an >= INT_MIN)) (PreH17 : (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) ((@nil (Z * Z)))))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) ((@nil (Z * Z)))))) )) (PreH18 : (an >= bn)) (PreH19 : (an = (Zabs (asize)))) (PreH20 : (bn = (Zabs (bsize)))) (PreH21 : (an <= acap)) (PreH22 : (bn <= bcap)) (PreH23 : (same_sign n_new asize )) (PreH24 : (same_sign m_new bsize )) (PreH25 : ((Zabs (rsize)) <= rcap)) (PreH26 : (same_sign l rsize )) (PreH27 : (rcap >= 0)) ,
  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (m_new)) bn )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
|--
  “ (((Zabs (asize)) + 1 ) >= 1) ” 
  &&  “ (((Zabs (asize)) + 1 ) <= INT_MAX) ” 
  &&  “ ((an + 1 ) <= INT_MAX) ” 
  &&  “ ((an + 1 ) >= 1) ”
).

Definition mpz_abs_add_partial_solve_wit_7_pure_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (n_new: Z) (m_new: Z) (aptr: Z) (bptr: Z) (asize: Z) (bsize: Z) (acap: Z) (bcap: Z) (rptr: Z) (rsize: Z) (rcap: Z) (b: Z) (a: Z) (an: Z) (bn: Z) (PreH1 : (rcap <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (bcap <= INT_MAX)) (PreH4 : (bsize <= INT_MAX)) (PreH5 : (acap <= INT_MAX)) (PreH6 : (asize <= INT_MAX)) (PreH7 : (bn <= INT_MAX)) (PreH8 : (an <= INT_MAX)) (PreH9 : (rcap >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bcap >= INT_MIN)) (PreH12 : (bsize >= INT_MIN)) (PreH13 : (acap >= INT_MIN)) (PreH14 : (asize >= INT_MIN)) (PreH15 : (bn >= INT_MIN)) (PreH16 : (an >= INT_MIN)) (PreH17 : (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) ((@nil (Z * Z)))))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) ((@nil (Z * Z)))))) )) (PreH18 : (an >= bn)) (PreH19 : (an = (Zabs (asize)))) (PreH20 : (bn = (Zabs (bsize)))) (PreH21 : (an <= acap)) (PreH22 : (bn <= bcap)) (PreH23 : (same_sign n_new asize )) (PreH24 : (same_sign m_new bsize )) (PreH25 : ((Zabs (rsize)) <= rcap)) (PreH26 : (same_sign l rsize )) (PreH27 : (rcap >= 0)) ,
  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (m_new)) bn )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
|--
  “ (((Zabs (asize)) + 1 ) >= 1) ”
.

Definition mpz_abs_add_partial_solve_wit_7_pure_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (n_new: Z) (m_new: Z) (aptr: Z) (bptr: Z) (asize: Z) (bsize: Z) (acap: Z) (bcap: Z) (rptr: Z) (rsize: Z) (rcap: Z) (b: Z) (a: Z) (an: Z) (bn: Z) (PreH1 : (rcap <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (bcap <= INT_MAX)) (PreH4 : (bsize <= INT_MAX)) (PreH5 : (acap <= INT_MAX)) (PreH6 : (asize <= INT_MAX)) (PreH7 : (bn <= INT_MAX)) (PreH8 : (an <= INT_MAX)) (PreH9 : (rcap >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bcap >= INT_MIN)) (PreH12 : (bsize >= INT_MIN)) (PreH13 : (acap >= INT_MIN)) (PreH14 : (asize >= INT_MIN)) (PreH15 : (bn >= INT_MIN)) (PreH16 : (an >= INT_MIN)) (PreH17 : (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) ((@nil (Z * Z)))))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) ((@nil (Z * Z)))))) )) (PreH18 : (an >= bn)) (PreH19 : (an = (Zabs (asize)))) (PreH20 : (bn = (Zabs (bsize)))) (PreH21 : (an <= acap)) (PreH22 : (bn <= bcap)) (PreH23 : (same_sign n_new asize )) (PreH24 : (same_sign m_new bsize )) (PreH25 : ((Zabs (rsize)) <= rcap)) (PreH26 : (same_sign l rsize )) (PreH27 : (rcap >= 0)) ,
  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (m_new)) bn )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
|--
  “ (((Zabs (asize)) + 1 ) <= INT_MAX) ”
.

Definition mpz_abs_add_partial_solve_wit_7_pure_split_goal_3 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (n_new: Z) (m_new: Z) (aptr: Z) (bptr: Z) (asize: Z) (bsize: Z) (acap: Z) (bcap: Z) (rptr: Z) (rsize: Z) (rcap: Z) (b: Z) (a: Z) (an: Z) (bn: Z) (PreH1 : (rcap <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (bcap <= INT_MAX)) (PreH4 : (bsize <= INT_MAX)) (PreH5 : (acap <= INT_MAX)) (PreH6 : (asize <= INT_MAX)) (PreH7 : (bn <= INT_MAX)) (PreH8 : (an <= INT_MAX)) (PreH9 : (rcap >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bcap >= INT_MIN)) (PreH12 : (bsize >= INT_MIN)) (PreH13 : (acap >= INT_MIN)) (PreH14 : (asize >= INT_MIN)) (PreH15 : (bn >= INT_MIN)) (PreH16 : (an >= INT_MIN)) (PreH17 : (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) ((@nil (Z * Z)))))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) ((@nil (Z * Z)))))) )) (PreH18 : (an >= bn)) (PreH19 : (an = (Zabs (asize)))) (PreH20 : (bn = (Zabs (bsize)))) (PreH21 : (an <= acap)) (PreH22 : (bn <= bcap)) (PreH23 : (same_sign n_new asize )) (PreH24 : (same_sign m_new bsize )) (PreH25 : ((Zabs (rsize)) <= rcap)) (PreH26 : (same_sign l rsize )) (PreH27 : (rcap >= 0)) ,
  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (m_new)) bn )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
|--
  “ ((an + 1 ) <= INT_MAX) ”
.

Definition mpz_abs_add_partial_solve_wit_7_pure_split_goal_4 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (n_new: Z) (m_new: Z) (aptr: Z) (bptr: Z) (asize: Z) (bsize: Z) (acap: Z) (bcap: Z) (rptr: Z) (rsize: Z) (rcap: Z) (b: Z) (a: Z) (an: Z) (bn: Z) (PreH1 : (rcap <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (bcap <= INT_MAX)) (PreH4 : (bsize <= INT_MAX)) (PreH5 : (acap <= INT_MAX)) (PreH6 : (asize <= INT_MAX)) (PreH7 : (bn <= INT_MAX)) (PreH8 : (an <= INT_MAX)) (PreH9 : (rcap >= INT_MIN)) (PreH10 : (rsize >= INT_MIN)) (PreH11 : (bcap >= INT_MIN)) (PreH12 : (bsize >= INT_MIN)) (PreH13 : (acap >= INT_MIN)) (PreH14 : (asize >= INT_MIN)) (PreH15 : (bn >= INT_MIN)) (PreH16 : (an >= INT_MIN)) (PreH17 : (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) ((@nil (Z * Z)))))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) ((@nil (Z * Z)))))) )) (PreH18 : (an >= bn)) (PreH19 : (an = (Zabs (asize)))) (PreH20 : (bn = (Zabs (bsize)))) (PreH21 : (an <= acap)) (PreH22 : (bn <= bcap)) (PreH23 : (same_sign n_new asize )) (PreH24 : (same_sign m_new bsize )) (PreH25 : ((Zabs (rsize)) <= rcap)) (PreH26 : (same_sign l rsize )) (PreH27 : (rcap >= 0)) ,
  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (m_new)) bn )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
|--
  “ ((an + 1 ) >= 1) ”
.

Definition mpz_abs_add_partial_solve_wit_7_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (n_new: Z) (m_new: Z) (aptr: Z) (bptr: Z) (asize: Z) (bsize: Z) (acap: Z) (bcap: Z) (rptr: Z) (rsize: Z) (rcap: Z) (b: Z) (a: Z) (an: Z) (bn: Z) (PreH1 : (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) ((@nil (Z * Z)))))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) ((@nil (Z * Z)))))) )) (PreH2 : (an >= bn)) (PreH3 : (an = (Zabs (asize)))) (PreH4 : (bn = (Zabs (bsize)))) (PreH5 : (an <= acap)) (PreH6 : (bn <= bcap)) (PreH7 : (same_sign n_new asize )) (PreH8 : (same_sign m_new bsize )) (PreH9 : ((Zabs (rsize)) <= rcap)) (PreH10 : (same_sign l rsize )) (PreH11 : (rcap >= 0)) ,
  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (m_new)) bn )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
|--
  “ (rcap >= 0) ” 
  &&  “ ((an + 1 ) >= 1) ” 
  &&  “ ((an + 1 ) <= INT_MAX) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ (((Zabs (asize)) + 1 ) <= INT_MAX) ” 
  &&  “ (((Zabs (asize)) + 1 ) >= 1) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) ((@nil (Z * Z)))))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) ((@nil (Z * Z)))))) ) ” 
  &&  “ (an >= bn) ” 
  &&  “ (an = (Zabs (asize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (an <= acap) ” 
  &&  “ (bn <= bcap) ” 
  &&  “ (same_sign n_new asize ) ” 
  &&  “ (same_sign m_new bsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ (rcap >= 0) ”
  &&  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (m_new)) bn )
.

Definition mpz_abs_add_partial_solve_wit_7 := mpz_abs_add_partial_solve_wit_7_pure -> mpz_abs_add_partial_solve_wit_7_aux.

Definition mpz_abs_add_partial_solve_wit_8_pure := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (n_new: Z) (m_new: Z) (aptr: Z) (bptr: Z) (asize: Z) (bsize: Z) (acap: Z) (bcap: Z) (rsize: Z) (rcap: Z) (b: Z) (a: Z) (an: Z) (bn: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (PreH1 : (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) ((@nil (Z * Z)))))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) ((@nil (Z * Z)))))) )) (PreH2 : (an >= bn)) (PreH3 : (an = (Zabs (asize)))) (PreH4 : (bn = (Zabs (bsize)))) (PreH5 : (an <= acap)) (PreH6 : (bn <= bcap)) (PreH7 : (same_sign n_new asize )) (PreH8 : (same_sign m_new bsize )) (PreH9 : (same_sign l rsize )) (PreH10 : ((Zabs (rsize)) <= rcap)) (PreH11 : (rcap >= 0)) (PreH12 : (r__mp_alloc = (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) (PreH13 : (r__mp_d = rp)) (PreH14 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH15 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) ,
  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (m_new)) bn )
  **  (UIntArray.undef_full rp an )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max ((an + 1 )) (1))) (rcap)) )
|--
  “ (an >= bn) ” 
  &&  “ (an >= 0) ” 
  &&  “ (bn >= 0) ” 
  &&  “ ((Zabs (bsize)) >= 0) ” 
  &&  “ ((Zabs (asize)) >= 0) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (n_new: Z) (m_new: Z) (aptr: Z) (bptr: Z) (asize: Z) (bsize: Z) (acap: Z) (bcap: Z) (rsize: Z) (rcap: Z) (b: Z) (a: Z) (an: Z) (bn: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (acap <= INT_MAX)) (PreH4 : (asize <= INT_MAX)) (PreH5 : (r__mp_alloc <= INT_MAX)) (PreH6 : (rsize <= INT_MAX)) (PreH7 : (bn <= INT_MAX)) (PreH8 : (an <= INT_MAX)) (PreH9 : (bcap >= INT_MIN)) (PreH10 : (bsize >= INT_MIN)) (PreH11 : (acap >= INT_MIN)) (PreH12 : (asize >= INT_MIN)) (PreH13 : (r__mp_alloc >= INT_MIN)) (PreH14 : (rsize >= INT_MIN)) (PreH15 : (bn >= INT_MIN)) (PreH16 : (an >= INT_MIN)) (PreH17 : (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) ((@nil (Z * Z)))))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) ((@nil (Z * Z)))))) )) (PreH18 : (an >= bn)) (PreH19 : (an = (Zabs (asize)))) (PreH20 : (bn = (Zabs (bsize)))) (PreH21 : (an <= acap)) (PreH22 : (bn <= bcap)) (PreH23 : (same_sign n_new asize )) (PreH24 : (same_sign m_new bsize )) (PreH25 : (same_sign l rsize )) (PreH26 : ((Zabs (rsize)) <= rcap)) (PreH27 : (rcap >= 0)) (PreH28 : (r__mp_alloc = (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) (PreH29 : (r__mp_d = rp)) (PreH30 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH31 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) ,
  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (m_new)) bn )
  **  (UIntArray.undef_full rp an )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max ((an + 1 )) (1))) (rcap)) )
|--
  “ ((Zabs (asize)) >= 0) ” 
  &&  “ ((Zabs (bsize)) >= 0) ” 
  &&  “ (bn >= 0) ” 
  &&  “ (an >= 0) ”
).

Definition mpz_abs_add_partial_solve_wit_8_pure_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (n_new: Z) (m_new: Z) (aptr: Z) (bptr: Z) (asize: Z) (bsize: Z) (acap: Z) (bcap: Z) (rsize: Z) (rcap: Z) (b: Z) (a: Z) (an: Z) (bn: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (acap <= INT_MAX)) (PreH4 : (asize <= INT_MAX)) (PreH5 : (r__mp_alloc <= INT_MAX)) (PreH6 : (rsize <= INT_MAX)) (PreH7 : (bn <= INT_MAX)) (PreH8 : (an <= INT_MAX)) (PreH9 : (bcap >= INT_MIN)) (PreH10 : (bsize >= INT_MIN)) (PreH11 : (acap >= INT_MIN)) (PreH12 : (asize >= INT_MIN)) (PreH13 : (r__mp_alloc >= INT_MIN)) (PreH14 : (rsize >= INT_MIN)) (PreH15 : (bn >= INT_MIN)) (PreH16 : (an >= INT_MIN)) (PreH17 : (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) ((@nil (Z * Z)))))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) ((@nil (Z * Z)))))) )) (PreH18 : (an >= bn)) (PreH19 : (an = (Zabs (asize)))) (PreH20 : (bn = (Zabs (bsize)))) (PreH21 : (an <= acap)) (PreH22 : (bn <= bcap)) (PreH23 : (same_sign n_new asize )) (PreH24 : (same_sign m_new bsize )) (PreH25 : (same_sign l rsize )) (PreH26 : ((Zabs (rsize)) <= rcap)) (PreH27 : (rcap >= 0)) (PreH28 : (r__mp_alloc = (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) (PreH29 : (r__mp_d = rp)) (PreH30 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH31 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) ,
  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (m_new)) bn )
  **  (UIntArray.undef_full rp an )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max ((an + 1 )) (1))) (rcap)) )
|--
  “ ((Zabs (asize)) >= 0) ”
.

Definition mpz_abs_add_partial_solve_wit_8_pure_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (n_new: Z) (m_new: Z) (aptr: Z) (bptr: Z) (asize: Z) (bsize: Z) (acap: Z) (bcap: Z) (rsize: Z) (rcap: Z) (b: Z) (a: Z) (an: Z) (bn: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (acap <= INT_MAX)) (PreH4 : (asize <= INT_MAX)) (PreH5 : (r__mp_alloc <= INT_MAX)) (PreH6 : (rsize <= INT_MAX)) (PreH7 : (bn <= INT_MAX)) (PreH8 : (an <= INT_MAX)) (PreH9 : (bcap >= INT_MIN)) (PreH10 : (bsize >= INT_MIN)) (PreH11 : (acap >= INT_MIN)) (PreH12 : (asize >= INT_MIN)) (PreH13 : (r__mp_alloc >= INT_MIN)) (PreH14 : (rsize >= INT_MIN)) (PreH15 : (bn >= INT_MIN)) (PreH16 : (an >= INT_MIN)) (PreH17 : (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) ((@nil (Z * Z)))))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) ((@nil (Z * Z)))))) )) (PreH18 : (an >= bn)) (PreH19 : (an = (Zabs (asize)))) (PreH20 : (bn = (Zabs (bsize)))) (PreH21 : (an <= acap)) (PreH22 : (bn <= bcap)) (PreH23 : (same_sign n_new asize )) (PreH24 : (same_sign m_new bsize )) (PreH25 : (same_sign l rsize )) (PreH26 : ((Zabs (rsize)) <= rcap)) (PreH27 : (rcap >= 0)) (PreH28 : (r__mp_alloc = (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) (PreH29 : (r__mp_d = rp)) (PreH30 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH31 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) ,
  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (m_new)) bn )
  **  (UIntArray.undef_full rp an )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max ((an + 1 )) (1))) (rcap)) )
|--
  “ ((Zabs (bsize)) >= 0) ”
.

Definition mpz_abs_add_partial_solve_wit_8_pure_split_goal_3 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (n_new: Z) (m_new: Z) (aptr: Z) (bptr: Z) (asize: Z) (bsize: Z) (acap: Z) (bcap: Z) (rsize: Z) (rcap: Z) (b: Z) (a: Z) (an: Z) (bn: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (acap <= INT_MAX)) (PreH4 : (asize <= INT_MAX)) (PreH5 : (r__mp_alloc <= INT_MAX)) (PreH6 : (rsize <= INT_MAX)) (PreH7 : (bn <= INT_MAX)) (PreH8 : (an <= INT_MAX)) (PreH9 : (bcap >= INT_MIN)) (PreH10 : (bsize >= INT_MIN)) (PreH11 : (acap >= INT_MIN)) (PreH12 : (asize >= INT_MIN)) (PreH13 : (r__mp_alloc >= INT_MIN)) (PreH14 : (rsize >= INT_MIN)) (PreH15 : (bn >= INT_MIN)) (PreH16 : (an >= INT_MIN)) (PreH17 : (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) ((@nil (Z * Z)))))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) ((@nil (Z * Z)))))) )) (PreH18 : (an >= bn)) (PreH19 : (an = (Zabs (asize)))) (PreH20 : (bn = (Zabs (bsize)))) (PreH21 : (an <= acap)) (PreH22 : (bn <= bcap)) (PreH23 : (same_sign n_new asize )) (PreH24 : (same_sign m_new bsize )) (PreH25 : (same_sign l rsize )) (PreH26 : ((Zabs (rsize)) <= rcap)) (PreH27 : (rcap >= 0)) (PreH28 : (r__mp_alloc = (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) (PreH29 : (r__mp_d = rp)) (PreH30 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH31 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) ,
  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (m_new)) bn )
  **  (UIntArray.undef_full rp an )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max ((an + 1 )) (1))) (rcap)) )
|--
  “ (bn >= 0) ”
.

Definition mpz_abs_add_partial_solve_wit_8_pure_split_goal_4 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (n_new: Z) (m_new: Z) (aptr: Z) (bptr: Z) (asize: Z) (bsize: Z) (acap: Z) (bcap: Z) (rsize: Z) (rcap: Z) (b: Z) (a: Z) (an: Z) (bn: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (PreH1 : (bcap <= INT_MAX)) (PreH2 : (bsize <= INT_MAX)) (PreH3 : (acap <= INT_MAX)) (PreH4 : (asize <= INT_MAX)) (PreH5 : (r__mp_alloc <= INT_MAX)) (PreH6 : (rsize <= INT_MAX)) (PreH7 : (bn <= INT_MAX)) (PreH8 : (an <= INT_MAX)) (PreH9 : (bcap >= INT_MIN)) (PreH10 : (bsize >= INT_MIN)) (PreH11 : (acap >= INT_MIN)) (PreH12 : (asize >= INT_MIN)) (PreH13 : (r__mp_alloc >= INT_MIN)) (PreH14 : (rsize >= INT_MIN)) (PreH15 : (bn >= INT_MIN)) (PreH16 : (an >= INT_MIN)) (PreH17 : (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) ((@nil (Z * Z)))))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) ((@nil (Z * Z)))))) )) (PreH18 : (an >= bn)) (PreH19 : (an = (Zabs (asize)))) (PreH20 : (bn = (Zabs (bsize)))) (PreH21 : (an <= acap)) (PreH22 : (bn <= bcap)) (PreH23 : (same_sign n_new asize )) (PreH24 : (same_sign m_new bsize )) (PreH25 : (same_sign l rsize )) (PreH26 : ((Zabs (rsize)) <= rcap)) (PreH27 : (rcap >= 0)) (PreH28 : (r__mp_alloc = (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) (PreH29 : (r__mp_d = rp)) (PreH30 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH31 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) ,
  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((( &( "a" ) )) # Ptr  |-> a)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (m_new)) bn )
  **  (UIntArray.undef_full rp an )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max ((an + 1 )) (1))) (rcap)) )
|--
  “ (an >= 0) ”
.

Definition mpz_abs_add_partial_solve_wit_8_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (n_new: Z) (m_new: Z) (aptr: Z) (bptr: Z) (asize: Z) (bsize: Z) (acap: Z) (bcap: Z) (rsize: Z) (rcap: Z) (b: Z) (a: Z) (an: Z) (bn: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (PreH1 : (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) ((@nil (Z * Z)))))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) ((@nil (Z * Z)))))) )) (PreH2 : (an >= bn)) (PreH3 : (an = (Zabs (asize)))) (PreH4 : (bn = (Zabs (bsize)))) (PreH5 : (an <= acap)) (PreH6 : (bn <= bcap)) (PreH7 : (same_sign n_new asize )) (PreH8 : (same_sign m_new bsize )) (PreH9 : (same_sign l rsize )) (PreH10 : ((Zabs (rsize)) <= rcap)) (PreH11 : (rcap >= 0)) (PreH12 : (r__mp_alloc = (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) (PreH13 : (r__mp_d = rp)) (PreH14 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH15 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
  **  (mpd_store_Z_compact UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z_compact UINT_MOD bptr (Zabs (m_new)) bn )
  **  (UIntArray.undef_full rp an )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max ((an + 1 )) (1))) (rcap)) )
|--
  “ (an >= bn) ” 
  &&  “ (an >= 0) ” 
  &&  “ (bn >= 0) ” 
  &&  “ ((Zabs (bsize)) >= 0) ” 
  &&  “ ((Zabs (asize)) >= 0) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (m_new)) bn ) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (n_new)) an ) ” 
  &&  “ (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) ((@nil (Z * Z)))))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) ((@nil (Z * Z)))))) ) ” 
  &&  “ (an >= bn) ” 
  &&  “ (an = (Zabs (asize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (an <= acap) ” 
  &&  “ (bn <= bcap) ” 
  &&  “ (same_sign n_new asize ) ” 
  &&  “ (same_sign m_new bsize ) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (r__mp_alloc = (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ” 
  &&  “ (r__mp_d = rp) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) ) ” 
  &&  “ (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ”
  &&  (mpd_store_Z UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z UINT_MOD bptr (Zabs (m_new)) bn )
  **  (UIntArray.undef_full rp an )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max ((an + 1 )) (1))) (rcap)) )
.

Definition mpz_abs_add_partial_solve_wit_8 := mpz_abs_add_partial_solve_wit_8_pure -> mpz_abs_add_partial_solve_wit_8_aux.

Definition mpz_abs_add_partial_solve_wit_9 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (n_new: Z) (m_new: Z) (aptr: Z) (bptr: Z) (asize: Z) (bsize: Z) (acap: Z) (bcap: Z) (rsize: Z) (rcap: Z) (b: Z) (a: Z) (an: Z) (bn: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (val_r_out: Z) (retval: Z) (PreH1 : ((val_r_out + (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (n_new)) + (Zabs (m_new)) ))) (PreH2 : (is_compact_Z UINT_MOD (Zabs (m_new)) bn )) (PreH3 : (is_compact_Z UINT_MOD (Zabs (n_new)) an )) (PreH4 : (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) ((@nil (Z * Z)))))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) ((@nil (Z * Z)))))) )) (PreH5 : (an >= bn)) (PreH6 : (an = (Zabs (asize)))) (PreH7 : (bn = (Zabs (bsize)))) (PreH8 : (an <= acap)) (PreH9 : (bn <= bcap)) (PreH10 : (same_sign n_new asize )) (PreH11 : (same_sign m_new bsize )) (PreH12 : (same_sign l rsize )) (PreH13 : ((Zabs (rsize)) <= rcap)) (PreH14 : (rcap >= 0)) (PreH15 : (r__mp_alloc = (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) (PreH16 : (r__mp_d = rp)) (PreH17 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH18 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) ,
  (mpd_store_Z UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z UINT_MOD bptr (Zabs (m_new)) bn )
  **  (mpd_store_Z UINT_MOD rp val_r_out an )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max ((an + 1 )) (1))) (rcap)) )
|--
  “ ((val_r_out + (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (n_new)) + (Zabs (m_new)) )) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (m_new)) bn ) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (n_new)) an ) ” 
  &&  “ (Permutation (cons ((Prod2 (a) (n_new))) ((cons ((Prod2 (b) (m_new))) ((@nil (Z * Z)))))) (cons ((Prod2 (a_pre) (n))) ((cons ((Prod2 (b_pre) (m))) ((@nil (Z * Z)))))) ) ” 
  &&  “ (an >= bn) ” 
  &&  “ (an = (Zabs (asize))) ” 
  &&  “ (bn = (Zabs (bsize))) ” 
  &&  “ (an <= acap) ” 
  &&  “ (bn <= bcap) ” 
  &&  “ (same_sign n_new asize ) ” 
  &&  “ (same_sign m_new bsize ) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (r__mp_alloc = (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ” 
  &&  “ (r__mp_d = rp) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) ) ” 
  &&  “ (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ”
  &&  (((rp + (an * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg rp (an + 1 ) (Z.max ((Z.max ((an + 1 )) (1))) (rcap)) )
  **  (mpd_store_Z UINT_MOD aptr (Zabs (n_new)) an )
  **  (mpd_store_Z UINT_MOD bptr (Zabs (m_new)) bn )
  **  (mpd_store_Z UINT_MOD rp val_r_out an )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> aptr)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> asize)
  **  ((&((a)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> acap)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> bptr)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> bsize)
  **  ((&((b)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> bcap)
  **  (UIntArray.undef_seg aptr an acap )
  **  (UIntArray.undef_seg bptr bn bcap )
.

(*----- Function mpz_abs_sub -----*)

Definition mpz_abs_sub_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (PreH1 : ((Zabs (n)) < (Zabs (m)))) (PreH2 : (retval_3 = (-1))) (PreH3 : (retval_2 = (Zabs (size_2)))) (PreH4 : (same_sign m size_2 )) (PreH5 : ((Zabs (size_2)) <= cap_2)) (PreH6 : (retval = (Zabs (size)))) (PreH7 : (same_sign n size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_abs_sub_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (PreH1 : ((Zabs (n)) = (Zabs (m)))) (PreH2 : (retval_3 = 0)) (PreH3 : (retval_2 = (Zabs (size_2)))) (PreH4 : (same_sign m size_2 )) (PreH5 : ((Zabs (size_2)) <= cap_2)) (PreH6 : (retval = (Zabs (size)))) (PreH7 : (same_sign n size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_abs_sub_safety_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (PreH1 : ((Zabs (n)) > (Zabs (m)))) (PreH2 : (retval_3 = 1)) (PreH3 : (retval_2 = (Zabs (size_2)))) (PreH4 : (same_sign m size_2 )) (PreH5 : ((Zabs (size_2)) <= cap_2)) (PreH6 : (retval = (Zabs (size)))) (PreH7 : (same_sign n size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_abs_sub_safety_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 > 0)) (PreH2 : ((Zabs (n)) < (Zabs (m)))) (PreH3 : (retval_3 = (-1))) (PreH4 : (retval_2 = (Zabs (size_2)))) (PreH5 : (same_sign m size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (retval = (Zabs (size)))) (PreH8 : (same_sign n size )) (PreH9 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ False ”
.

Definition mpz_abs_sub_safety_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 > 0)) (PreH2 : ((Zabs (n)) = (Zabs (m)))) (PreH3 : (retval_3 = 0)) (PreH4 : (retval_2 = (Zabs (size_2)))) (PreH5 : (same_sign m size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (retval = (Zabs (size)))) (PreH8 : (same_sign n size )) (PreH9 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ False ”
.

Definition mpz_abs_sub_safety_wit_6 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <= 0)) (PreH2 : ((Zabs (n)) > (Zabs (m)))) (PreH3 : (retval_3 = 1)) (PreH4 : (retval_2 = (Zabs (size_2)))) (PreH5 : (same_sign m size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (retval = (Zabs (size)))) (PreH8 : (same_sign n size )) (PreH9 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ False ”
.

Definition mpz_abs_sub_safety_wit_7 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <= 0)) (PreH2 : ((Zabs (n)) < (Zabs (m)))) (PreH3 : (retval_3 = (-1))) (PreH4 : (retval_2 = (Zabs (size_2)))) (PreH5 : (same_sign m size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (retval = (Zabs (size)))) (PreH8 : (same_sign n size )) (PreH9 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_abs_sub_safety_wit_8 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <= 0)) (PreH2 : ((Zabs (n)) = (Zabs (m)))) (PreH3 : (retval_3 = 0)) (PreH4 : (retval_2 = (Zabs (size_2)))) (PreH5 : (same_sign m size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (retval = (Zabs (size)))) (PreH8 : (same_sign n size )) (PreH9 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_abs_sub_safety_wit_9 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 >= 0)) (PreH2 : (retval_3 <= 0)) (PreH3 : ((Zabs (n)) < (Zabs (m)))) (PreH4 : (retval_3 = (-1))) (PreH5 : (retval_2 = (Zabs (size_2)))) (PreH6 : (same_sign m size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (retval = (Zabs (size)))) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ False ”
.

Definition mpz_abs_sub_safety_wit_10 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 < 0)) (PreH2 : (retval_3 <= 0)) (PreH3 : ((Zabs (n)) = (Zabs (m)))) (PreH4 : (retval_3 = 0)) (PreH5 : (retval_2 = (Zabs (size_2)))) (PreH6 : (same_sign m size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (retval = (Zabs (size)))) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ False ”
.

Definition mpz_abs_sub_safety_wit_11 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (val_r_out: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= bn)) (PreH3 : ((val_r_out - (retval_2 * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (m)) - (Zabs (n)) ))) (PreH4 : (is_compact_Z UINT_MOD (Zabs (m)) bn )) (PreH5 : (is_compact_Z UINT_MOD (Zabs (n)) an )) (PreH6 : (cmp < 0)) (PreH7 : (cmp <= 0)) (PreH8 : ((Zabs (n)) < (Zabs (m)))) (PreH9 : (cmp = (-1))) (PreH10 : (bn = (Zabs (b_pre__mp_size)))) (PreH11 : (same_sign m b_pre__mp_size )) (PreH12 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH13 : (an = (Zabs (a_pre__mp_size)))) (PreH14 : (same_sign n a_pre__mp_size )) (PreH15 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH16 : (same_sign l rsize )) (PreH17 : ((Zabs (rsize)) <= rcap)) (PreH18 : (rcap >= 0)) (PreH19 : (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap)))) (PreH20 : (r__mp_d = rp)) (PreH21 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH22 : (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap)))) ,
  (mpd_store_Z_compact UINT_MOD rp val_r_out retval )
  **  (UIntArray.undef_seg rp retval bn )
  **  (mpd_store_Z UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (mpd_store_Z UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  “ (retval <> (INT_MIN)) ”
.

Definition mpz_abs_sub_safety_wit_12 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 >= 0)) (PreH2 : (retval_3 <= 0)) (PreH3 : ((Zabs (n)) = (Zabs (m)))) (PreH4 : (retval_3 = 0)) (PreH5 : (retval_2 = (Zabs (size_2)))) (PreH6 : (same_sign m size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (retval = (Zabs (size)))) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |-> retval_3)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_abs_sub_entail_wit_1 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 > 0)) (PreH2 : ((Zabs (n)) > (Zabs (m)))) (PreH3 : (retval_3 = 1)) (PreH4 : (retval_2 = (Zabs (size_2)))) (PreH5 : (same_sign m size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (retval = (Zabs (size)))) (PreH8 : (same_sign n size )) (PreH9 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
|--
  EX (rptr: Z)  (b_pre__mp_d: Z)  (a_pre__mp_d: Z)  (rcap: Z)  (rsize: Z)  (a_pre__mp_alloc: Z)  (a_pre__mp_size: Z)  (b_pre__mp_alloc: Z)  (b_pre__mp_size: Z) ,
  “ (retval_3 > 0) ” 
  &&  “ ((Zabs (n)) > (Zabs (m))) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (retval_2 = (Zabs (b_pre__mp_size))) ” 
  &&  “ (same_sign m b_pre__mp_size ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc) ” 
  &&  “ (retval = (Zabs (a_pre__mp_size))) ” 
  &&  “ (same_sign n a_pre__mp_size ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ (rcap >= 0) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) retval )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) retval_2 )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
) \/
(
forall (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (ptr_3: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign l size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : (retval_3 > 0)) (PreH4 : ((Zabs (n)) > (Zabs (m)))) (PreH5 : (retval_3 = 1)) (PreH6 : (retval_2 = (Zabs (size_2)))) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (retval = (Zabs (size)))) (PreH10 : (same_sign n size )) (PreH11 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs (l)) (Zabs (size_3)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
|--
  “ (cap_3 >= 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs (l)) (Zabs (size_3)) )
).

Definition mpz_abs_sub_entail_wit_1_split_goal_1 := 
forall (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (ptr_3: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign l size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : (retval_3 > 0)) (PreH4 : ((Zabs (n)) > (Zabs (m)))) (PreH5 : (retval_3 = 1)) (PreH6 : (retval_2 = (Zabs (size_2)))) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (retval = (Zabs (size)))) (PreH10 : (same_sign n size )) (PreH11 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs (l)) (Zabs (size_3)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
|--
  “ (cap_3 >= 0) ”
.

Definition mpz_abs_sub_entail_wit_1_split_goal_spatial := 
forall (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (ptr_3: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign l size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : (retval_3 > 0)) (PreH4 : ((Zabs (n)) > (Zabs (m)))) (PreH5 : (retval_3 = 1)) (PreH6 : (retval_2 = (Zabs (size_2)))) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (retval = (Zabs (size)))) (PreH10 : (same_sign n size )) (PreH11 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs (l)) (Zabs (size_3)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
|--
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs (l)) (Zabs (size_3)) )
.

Definition mpz_abs_sub_entail_wit_2 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize_2: Z) (rcap_2: Z) (cmp: Z) (bn: Z) (b_pre__mp_size_2: Z) (b_pre__mp_alloc_2: Z) (an: Z) (a_pre__mp_size_2: Z) (a_pre__mp_alloc_2: Z) (a_pre__mp_d_2: Z) (b_pre__mp_d_2: Z) (z_callee__mp_alloc: Z) (retval: Z) (PreH1 : (same_sign l rsize_2 )) (PreH2 : (z_callee__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap_2)))) (PreH3 : (cmp > 0)) (PreH4 : ((Zabs (n)) > (Zabs (m)))) (PreH5 : (cmp = 1)) (PreH6 : (bn = (Zabs (b_pre__mp_size_2)))) (PreH7 : (same_sign m b_pre__mp_size_2 )) (PreH8 : ((Zabs (b_pre__mp_size_2)) <= b_pre__mp_alloc_2)) (PreH9 : (an = (Zabs (a_pre__mp_size_2)))) (PreH10 : (same_sign n a_pre__mp_size_2 )) (PreH11 : ((Zabs (a_pre__mp_size_2)) <= a_pre__mp_alloc_2)) (PreH12 : ((Zabs (rsize_2)) <= rcap_2)) (PreH13 : (same_sign l rsize_2 )) (PreH14 : (rcap_2 >= 0)) ,
  (mpd_store_Z_compact UINT_MOD retval (Zabs (l)) (Zabs (rsize_2)) )
  **  (UIntArray.undef_seg retval (Zabs (rsize_2)) (Z.max ((Z.max (an) (1))) (rcap_2)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_callee__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d_2)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d_2 (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d_2)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d_2 (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d_2 (Zabs (b_pre__mp_size_2)) b_pre__mp_alloc_2 )
  **  (UIntArray.undef_seg a_pre__mp_d_2 (Zabs (a_pre__mp_size_2)) a_pre__mp_alloc_2 )
|--
  EX (b_pre__mp_d: Z)  (a_pre__mp_d: Z)  (r__mp_d: Z)  (r__mp_alloc: Z)  (rcap: Z)  (rsize: Z)  (a_pre__mp_alloc: Z)  (a_pre__mp_size: Z)  (b_pre__mp_alloc: Z)  (b_pre__mp_size: Z) ,
  “ (cmp > 0) ” 
  &&  “ ((Zabs (n)) > (Zabs (m))) ” 
  &&  “ (cmp = 1) ” 
  &&  “ (bn = (Zabs (b_pre__mp_size))) ” 
  &&  “ (same_sign m b_pre__mp_size ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc) ” 
  &&  “ (an = (Zabs (a_pre__mp_size))) ” 
  &&  “ (same_sign n a_pre__mp_size ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap))) ” 
  &&  “ (r__mp_d = retval) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) ) ” 
  &&  “ (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  (UIntArray.undef_full retval an )
  **  (UIntArray.undef_seg retval an (Z.max ((Z.max (an) (1))) (rcap)) )
) \/
(
forall (l: Z) (m: Z) (n: Z) (rsize_2: Z) (rcap_2: Z) (cmp: Z) (bn: Z) (b_pre__mp_size_2: Z) (b_pre__mp_alloc_2: Z) (an: Z) (a_pre__mp_size_2: Z) (a_pre__mp_alloc_2: Z) (a_pre__mp_d_2: Z) (b_pre__mp_d_2: Z) (z_callee__mp_alloc: Z) (retval: Z) (PreH1 : (same_sign l rsize_2 )) (PreH2 : (z_callee__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap_2)))) (PreH3 : (cmp > 0)) (PreH4 : ((Zabs (n)) > (Zabs (m)))) (PreH5 : (cmp = 1)) (PreH6 : (bn = (Zabs (b_pre__mp_size_2)))) (PreH7 : (same_sign m b_pre__mp_size_2 )) (PreH8 : ((Zabs (b_pre__mp_size_2)) <= b_pre__mp_alloc_2)) (PreH9 : (an = (Zabs (a_pre__mp_size_2)))) (PreH10 : (same_sign n a_pre__mp_size_2 )) (PreH11 : ((Zabs (a_pre__mp_size_2)) <= a_pre__mp_alloc_2)) (PreH12 : ((Zabs (rsize_2)) <= rcap_2)) (PreH13 : (same_sign l rsize_2 )) (PreH14 : (rcap_2 >= 0)) ,
  (mpd_store_Z_compact UINT_MOD retval (Zabs (l)) (Zabs (rsize_2)) )
  **  (UIntArray.undef_seg retval (Zabs (rsize_2)) (Z.max ((Z.max (an) (1))) (rcap_2)) )
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d_2 (Zabs (n)) an )
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d_2 (Zabs (m)) bn )
|--
  EX (rcap: Z) ,
  “ (z_callee__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap))) ” 
  &&  “ (z_callee__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap))) ” 
  &&  “ (cmp > 0) ” 
  &&  “ ((Zabs (n)) > (Zabs (m))) ” 
  &&  “ (cmp = 1) ” 
  &&  “ (bn = (Zabs (b_pre__mp_size_2))) ” 
  &&  “ (same_sign m b_pre__mp_size_2 ) ” 
  &&  “ ((Zabs (b_pre__mp_size_2)) <= b_pre__mp_alloc_2) ” 
  &&  “ (an = (Zabs (a_pre__mp_size_2))) ” 
  &&  “ (same_sign n a_pre__mp_size_2 ) ” 
  &&  “ ((Zabs (a_pre__mp_size_2)) <= a_pre__mp_alloc_2) ” 
  &&  “ (same_sign l rsize_2 ) ” 
  &&  “ ((Zabs (rsize_2)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize_2)) ) ” 
  &&  “ (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ”
  &&  (mpd_store_Z_compact UINT_MOD a_pre__mp_d_2 (Zabs (n)) an )
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d_2 (Zabs (m)) bn )
  **  (UIntArray.undef_full retval an )
  **  (UIntArray.undef_seg retval an (Z.max ((Z.max (an) (1))) (rcap)) )
).

Definition mpz_abs_sub_entail_wit_3 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 < 0)) (PreH2 : (retval_3 <= 0)) (PreH3 : ((Zabs (n)) < (Zabs (m)))) (PreH4 : (retval_3 = (-1))) (PreH5 : (retval_2 = (Zabs (size_2)))) (PreH6 : (same_sign m size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (retval = (Zabs (size)))) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
|--
  EX (rptr: Z)  (b_pre__mp_d: Z)  (a_pre__mp_d: Z)  (rcap: Z)  (rsize: Z)  (a_pre__mp_alloc: Z)  (a_pre__mp_size: Z)  (b_pre__mp_alloc: Z)  (b_pre__mp_size: Z) ,
  “ (retval_3 < 0) ” 
  &&  “ (retval_3 <= 0) ” 
  &&  “ ((Zabs (n)) < (Zabs (m))) ” 
  &&  “ (retval_3 = (-1)) ” 
  &&  “ (retval_2 = (Zabs (b_pre__mp_size))) ” 
  &&  “ (same_sign m b_pre__mp_size ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc) ” 
  &&  “ (retval = (Zabs (a_pre__mp_size))) ” 
  &&  “ (same_sign n a_pre__mp_size ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ (rcap >= 0) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) retval )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) retval_2 )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
) \/
(
forall (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (ptr_3: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign l size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : (retval_3 < 0)) (PreH4 : (retval_3 <= 0)) (PreH5 : ((Zabs (n)) < (Zabs (m)))) (PreH6 : (retval_3 = (-1))) (PreH7 : (retval_2 = (Zabs (size_2)))) (PreH8 : (same_sign m size_2 )) (PreH9 : ((Zabs (size_2)) <= cap_2)) (PreH10 : (retval = (Zabs (size)))) (PreH11 : (same_sign n size )) (PreH12 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs (l)) (Zabs (size_3)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
|--
  “ (cap_3 >= 0) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs (l)) (Zabs (size_3)) )
).

Definition mpz_abs_sub_entail_wit_3_split_goal_1 := 
forall (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (ptr_3: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign l size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : (retval_3 < 0)) (PreH4 : (retval_3 <= 0)) (PreH5 : ((Zabs (n)) < (Zabs (m)))) (PreH6 : (retval_3 = (-1))) (PreH7 : (retval_2 = (Zabs (size_2)))) (PreH8 : (same_sign m size_2 )) (PreH9 : ((Zabs (size_2)) <= cap_2)) (PreH10 : (retval = (Zabs (size)))) (PreH11 : (same_sign n size )) (PreH12 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs (l)) (Zabs (size_3)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
|--
  “ (cap_3 >= 0) ”
.

Definition mpz_abs_sub_entail_wit_3_split_goal_spatial := 
forall (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (ptr_3: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign l size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : (retval_3 < 0)) (PreH4 : (retval_3 <= 0)) (PreH5 : ((Zabs (n)) < (Zabs (m)))) (PreH6 : (retval_3 = (-1))) (PreH7 : (retval_2 = (Zabs (size_2)))) (PreH8 : (same_sign m size_2 )) (PreH9 : ((Zabs (size_2)) <= cap_2)) (PreH10 : (retval = (Zabs (size)))) (PreH11 : (same_sign n size )) (PreH12 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs (l)) (Zabs (size_3)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
|--
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_3 (Zabs (l)) (Zabs (size_3)) )
.

Definition mpz_abs_sub_entail_wit_4 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize_2: Z) (rcap_2: Z) (cmp: Z) (bn: Z) (b_pre__mp_size_2: Z) (b_pre__mp_alloc_2: Z) (an: Z) (a_pre__mp_size_2: Z) (a_pre__mp_alloc_2: Z) (a_pre__mp_d_2: Z) (b_pre__mp_d_2: Z) (z_callee__mp_alloc: Z) (retval: Z) (PreH1 : (same_sign l rsize_2 )) (PreH2 : (z_callee__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap_2)))) (PreH3 : (cmp < 0)) (PreH4 : (cmp <= 0)) (PreH5 : ((Zabs (n)) < (Zabs (m)))) (PreH6 : (cmp = (-1))) (PreH7 : (bn = (Zabs (b_pre__mp_size_2)))) (PreH8 : (same_sign m b_pre__mp_size_2 )) (PreH9 : ((Zabs (b_pre__mp_size_2)) <= b_pre__mp_alloc_2)) (PreH10 : (an = (Zabs (a_pre__mp_size_2)))) (PreH11 : (same_sign n a_pre__mp_size_2 )) (PreH12 : ((Zabs (a_pre__mp_size_2)) <= a_pre__mp_alloc_2)) (PreH13 : ((Zabs (rsize_2)) <= rcap_2)) (PreH14 : (same_sign l rsize_2 )) (PreH15 : (rcap_2 >= 0)) ,
  (mpd_store_Z_compact UINT_MOD retval (Zabs (l)) (Zabs (rsize_2)) )
  **  (UIntArray.undef_seg retval (Zabs (rsize_2)) (Z.max ((Z.max (bn) (1))) (rcap_2)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_callee__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d_2)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d_2 (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d_2)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d_2 (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d_2 (Zabs (b_pre__mp_size_2)) b_pre__mp_alloc_2 )
  **  (UIntArray.undef_seg a_pre__mp_d_2 (Zabs (a_pre__mp_size_2)) a_pre__mp_alloc_2 )
|--
  EX (b_pre__mp_d: Z)  (a_pre__mp_d: Z)  (r__mp_d: Z)  (r__mp_alloc: Z)  (rcap: Z)  (rsize: Z)  (a_pre__mp_alloc: Z)  (a_pre__mp_size: Z)  (b_pre__mp_alloc: Z)  (b_pre__mp_size: Z) ,
  “ (cmp < 0) ” 
  &&  “ (cmp <= 0) ” 
  &&  “ ((Zabs (n)) < (Zabs (m))) ” 
  &&  “ (cmp = (-1)) ” 
  &&  “ (bn = (Zabs (b_pre__mp_size))) ” 
  &&  “ (same_sign m b_pre__mp_size ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc) ” 
  &&  “ (an = (Zabs (a_pre__mp_size))) ” 
  &&  “ (same_sign n a_pre__mp_size ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap))) ” 
  &&  “ (r__mp_d = retval) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) ) ” 
  &&  “ (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap))) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  (UIntArray.undef_full retval bn )
  **  (UIntArray.undef_seg retval bn (Z.max ((Z.max (bn) (1))) (rcap)) )
) \/
(
forall (l: Z) (m: Z) (n: Z) (rsize_2: Z) (rcap_2: Z) (cmp: Z) (bn: Z) (b_pre__mp_size_2: Z) (b_pre__mp_alloc_2: Z) (an: Z) (a_pre__mp_size_2: Z) (a_pre__mp_alloc_2: Z) (a_pre__mp_d_2: Z) (b_pre__mp_d_2: Z) (z_callee__mp_alloc: Z) (retval: Z) (PreH1 : (same_sign l rsize_2 )) (PreH2 : (z_callee__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap_2)))) (PreH3 : (cmp < 0)) (PreH4 : (cmp <= 0)) (PreH5 : ((Zabs (n)) < (Zabs (m)))) (PreH6 : (cmp = (-1))) (PreH7 : (bn = (Zabs (b_pre__mp_size_2)))) (PreH8 : (same_sign m b_pre__mp_size_2 )) (PreH9 : ((Zabs (b_pre__mp_size_2)) <= b_pre__mp_alloc_2)) (PreH10 : (an = (Zabs (a_pre__mp_size_2)))) (PreH11 : (same_sign n a_pre__mp_size_2 )) (PreH12 : ((Zabs (a_pre__mp_size_2)) <= a_pre__mp_alloc_2)) (PreH13 : ((Zabs (rsize_2)) <= rcap_2)) (PreH14 : (same_sign l rsize_2 )) (PreH15 : (rcap_2 >= 0)) ,
  (mpd_store_Z_compact UINT_MOD retval (Zabs (l)) (Zabs (rsize_2)) )
  **  (UIntArray.undef_seg retval (Zabs (rsize_2)) (Z.max ((Z.max (bn) (1))) (rcap_2)) )
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d_2 (Zabs (n)) an )
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d_2 (Zabs (m)) bn )
|--
  EX (rcap: Z) ,
  “ (z_callee__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap))) ” 
  &&  “ (z_callee__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap))) ” 
  &&  “ (cmp < 0) ” 
  &&  “ (cmp <= 0) ” 
  &&  “ ((Zabs (n)) < (Zabs (m))) ” 
  &&  “ (cmp = (-1)) ” 
  &&  “ (bn = (Zabs (b_pre__mp_size_2))) ” 
  &&  “ (same_sign m b_pre__mp_size_2 ) ” 
  &&  “ ((Zabs (b_pre__mp_size_2)) <= b_pre__mp_alloc_2) ” 
  &&  “ (an = (Zabs (a_pre__mp_size_2))) ” 
  &&  “ (same_sign n a_pre__mp_size_2 ) ” 
  &&  “ ((Zabs (a_pre__mp_size_2)) <= a_pre__mp_alloc_2) ” 
  &&  “ (same_sign l rsize_2 ) ” 
  &&  “ ((Zabs (rsize_2)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize_2)) ) ” 
  &&  “ (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap))) ”
  &&  (mpd_store_Z_compact UINT_MOD a_pre__mp_d_2 (Zabs (n)) an )
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d_2 (Zabs (m)) bn )
  **  (UIntArray.undef_full retval bn )
  **  (UIntArray.undef_seg retval bn (Z.max ((Z.max (bn) (1))) (rcap)) )
).

Definition mpz_abs_sub_return_wit_1 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 >= 0)) (PreH2 : (retval_3 <= 0)) (PreH3 : ((Zabs (n)) = (Zabs (m)))) (PreH4 : (retval_3 = 0)) (PreH5 : (retval_2 = (Zabs (size_2)))) (PreH6 : (same_sign m size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (retval = (Zabs (size)))) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
|--
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) 0 )
) \/
(
forall (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 >= 0)) (PreH2 : (retval_3 <= 0)) (PreH3 : ((Zabs (n)) = (Zabs (m)))) (PreH4 : (retval_3 = 0)) (PreH5 : (retval_2 = (Zabs (size_2)))) (PreH6 : (same_sign m size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (retval = (Zabs (size)))) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  (store_Z r_pre l )
|--
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) 0 )
).

Definition mpz_abs_sub_return_wit_1_split_goal_spatial := 
forall (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 >= 0)) (PreH2 : (retval_3 <= 0)) (PreH3 : ((Zabs (n)) = (Zabs (m)))) (PreH4 : (retval_3 = 0)) (PreH5 : (retval_2 = (Zabs (size_2)))) (PreH6 : (same_sign m size_2 )) (PreH7 : ((Zabs (size_2)) <= cap_2)) (PreH8 : (retval = (Zabs (size)))) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  (store_Z r_pre l )
|--
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) 0 )
.

Definition mpz_abs_sub_return_wit_2 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (val_r_out: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= bn)) (PreH3 : ((val_r_out - (retval_2 * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (m)) - (Zabs (n)) ))) (PreH4 : (is_compact_Z UINT_MOD (Zabs (m)) bn )) (PreH5 : (is_compact_Z UINT_MOD (Zabs (n)) an )) (PreH6 : (cmp < 0)) (PreH7 : (cmp <= 0)) (PreH8 : ((Zabs (n)) < (Zabs (m)))) (PreH9 : (cmp = (-1))) (PreH10 : (bn = (Zabs (b_pre__mp_size)))) (PreH11 : (same_sign m b_pre__mp_size )) (PreH12 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH13 : (an = (Zabs (a_pre__mp_size)))) (PreH14 : (same_sign n a_pre__mp_size )) (PreH15 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH16 : (same_sign l rsize )) (PreH17 : ((Zabs (rsize)) <= rcap)) (PreH18 : (rcap >= 0)) (PreH19 : (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap)))) (PreH20 : (r__mp_d = rp)) (PreH21 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH22 : (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap)))) ,
  (mpd_store_Z_compact UINT_MOD rp val_r_out retval )
  **  (UIntArray.undef_seg rp retval bn )
  **  (mpd_store_Z UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (mpd_store_Z UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) (-retval) )
) \/
(
forall (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (val_r_out: Z) (retval_2: Z) (retval: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (r__mp_alloc >= INT_MIN)) (PreH4 : (rsize >= INT_MIN)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= bn)) (PreH7 : ((val_r_out - (retval_2 * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (m)) - (Zabs (n)) ))) (PreH8 : (is_compact_Z UINT_MOD (Zabs (m)) bn )) (PreH9 : (is_compact_Z UINT_MOD (Zabs (n)) an )) (PreH10 : (cmp < 0)) (PreH11 : (cmp <= 0)) (PreH12 : ((Zabs (n)) < (Zabs (m)))) (PreH13 : (cmp = (-1))) (PreH14 : (bn = (Zabs (b_pre__mp_size)))) (PreH15 : (same_sign m b_pre__mp_size )) (PreH16 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH17 : (an = (Zabs (a_pre__mp_size)))) (PreH18 : (same_sign n a_pre__mp_size )) (PreH19 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH20 : (same_sign l rsize )) (PreH21 : ((Zabs (rsize)) <= rcap)) (PreH22 : (rcap >= 0)) (PreH23 : (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap)))) (PreH24 : (r__mp_d = rp)) (PreH25 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH26 : (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap)))) ,
  (mpd_store_Z_compact UINT_MOD rp val_r_out retval )
  **  (UIntArray.undef_seg rp retval bn )
  **  (mpd_store_Z UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (mpd_store_Z UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) (Zabs (b_pre__mp_size)) )
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) (Zabs (a_pre__mp_size)) )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) (-retval) )
).

Definition mpz_abs_sub_return_wit_2_split_goal_spatial := 
forall (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (val_r_out: Z) (retval_2: Z) (retval: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (r__mp_alloc >= INT_MIN)) (PreH4 : (rsize >= INT_MIN)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= bn)) (PreH7 : ((val_r_out - (retval_2 * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (m)) - (Zabs (n)) ))) (PreH8 : (is_compact_Z UINT_MOD (Zabs (m)) bn )) (PreH9 : (is_compact_Z UINT_MOD (Zabs (n)) an )) (PreH10 : (cmp < 0)) (PreH11 : (cmp <= 0)) (PreH12 : ((Zabs (n)) < (Zabs (m)))) (PreH13 : (cmp = (-1))) (PreH14 : (bn = (Zabs (b_pre__mp_size)))) (PreH15 : (same_sign m b_pre__mp_size )) (PreH16 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH17 : (an = (Zabs (a_pre__mp_size)))) (PreH18 : (same_sign n a_pre__mp_size )) (PreH19 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH20 : (same_sign l rsize )) (PreH21 : ((Zabs (rsize)) <= rcap)) (PreH22 : (rcap >= 0)) (PreH23 : (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap)))) (PreH24 : (r__mp_d = rp)) (PreH25 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH26 : (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap)))) ,
  (mpd_store_Z_compact UINT_MOD rp val_r_out retval )
  **  (UIntArray.undef_seg rp retval bn )
  **  (mpd_store_Z UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (mpd_store_Z UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) (Zabs (b_pre__mp_size)) )
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) (Zabs (a_pre__mp_size)) )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) (-retval) )
.

Definition mpz_abs_sub_return_wit_3 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (val_r_out: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= an)) (PreH3 : ((val_r_out - (retval_2 * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (n)) - (Zabs (m)) ))) (PreH4 : (is_compact_Z UINT_MOD (Zabs (m)) bn )) (PreH5 : (is_compact_Z UINT_MOD (Zabs (n)) an )) (PreH6 : (cmp > 0)) (PreH7 : ((Zabs (n)) > (Zabs (m)))) (PreH8 : (cmp = 1)) (PreH9 : (bn = (Zabs (b_pre__mp_size)))) (PreH10 : (same_sign m b_pre__mp_size )) (PreH11 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH12 : (an = (Zabs (a_pre__mp_size)))) (PreH13 : (same_sign n a_pre__mp_size )) (PreH14 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH15 : (same_sign l rsize )) (PreH16 : ((Zabs (rsize)) <= rcap)) (PreH17 : (rcap >= 0)) (PreH18 : (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap)))) (PreH19 : (r__mp_d = rp)) (PreH20 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH21 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) ,
  (mpd_store_Z_compact UINT_MOD rp val_r_out retval )
  **  (UIntArray.undef_seg rp retval an )
  **  (mpd_store_Z UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  (mpd_store_Z UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
|--
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) retval )
) \/
(
forall (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (val_r_out: Z) (retval_2: Z) (retval: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (r__mp_alloc >= INT_MIN)) (PreH4 : (rsize >= INT_MIN)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= an)) (PreH7 : ((val_r_out - (retval_2 * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (n)) - (Zabs (m)) ))) (PreH8 : (is_compact_Z UINT_MOD (Zabs (m)) bn )) (PreH9 : (is_compact_Z UINT_MOD (Zabs (n)) an )) (PreH10 : (cmp > 0)) (PreH11 : ((Zabs (n)) > (Zabs (m)))) (PreH12 : (cmp = 1)) (PreH13 : (bn = (Zabs (b_pre__mp_size)))) (PreH14 : (same_sign m b_pre__mp_size )) (PreH15 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH16 : (an = (Zabs (a_pre__mp_size)))) (PreH17 : (same_sign n a_pre__mp_size )) (PreH18 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH19 : (same_sign l rsize )) (PreH20 : ((Zabs (rsize)) <= rcap)) (PreH21 : (rcap >= 0)) (PreH22 : (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap)))) (PreH23 : (r__mp_d = rp)) (PreH24 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH25 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) ,
  (mpd_store_Z_compact UINT_MOD rp val_r_out retval )
  **  (UIntArray.undef_seg rp retval an )
  **  (mpd_store_Z UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  (mpd_store_Z UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
|--
  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) (Zabs (b_pre__mp_size)) )
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) (Zabs (a_pre__mp_size)) )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) retval )
).

Definition mpz_abs_sub_return_wit_3_split_goal_spatial := 
forall (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (val_r_out: Z) (retval_2: Z) (retval: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (r__mp_alloc >= INT_MIN)) (PreH4 : (rsize >= INT_MIN)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= an)) (PreH7 : ((val_r_out - (retval_2 * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (n)) - (Zabs (m)) ))) (PreH8 : (is_compact_Z UINT_MOD (Zabs (m)) bn )) (PreH9 : (is_compact_Z UINT_MOD (Zabs (n)) an )) (PreH10 : (cmp > 0)) (PreH11 : ((Zabs (n)) > (Zabs (m)))) (PreH12 : (cmp = 1)) (PreH13 : (bn = (Zabs (b_pre__mp_size)))) (PreH14 : (same_sign m b_pre__mp_size )) (PreH15 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH16 : (an = (Zabs (a_pre__mp_size)))) (PreH17 : (same_sign n a_pre__mp_size )) (PreH18 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH19 : (same_sign l rsize )) (PreH20 : ((Zabs (rsize)) <= rcap)) (PreH21 : (rcap >= 0)) (PreH22 : (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap)))) (PreH23 : (r__mp_d = rp)) (PreH24 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH25 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) ,
  (mpd_store_Z_compact UINT_MOD rp val_r_out retval )
  **  (UIntArray.undef_seg rp retval an )
  **  (mpd_store_Z UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  (mpd_store_Z UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
|--
  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) (Zabs (b_pre__mp_size)) )
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) (Zabs (a_pre__mp_size)) )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) retval )
.

Definition mpz_abs_sub_partial_solve_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) ,
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
|--
  EX (cap: Z)  (size: Z)  (ptr: Z) ,
  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
.

Definition mpz_abs_sub_partial_solve_wit_2_pure := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign n size )) (PreH2 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
|--
  “ (size <= INT_MAX) ” 
  &&  “ (INT_MIN < size) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (cap <= INT_MAX)) (PreH2 : (size <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : (size >= INT_MIN)) (PreH5 : (same_sign n size )) (PreH6 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
|--
  “ (INT_MIN < size) ”
).

Definition mpz_abs_sub_partial_solve_wit_2_pure_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (cap <= INT_MAX)) (PreH2 : (size <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : (size >= INT_MIN)) (PreH5 : (same_sign n size )) (PreH6 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
|--
  “ (INT_MIN < size) ”
.

Definition mpz_abs_sub_partial_solve_wit_2_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign n size )) (PreH2 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
|--
  “ (size <= INT_MAX) ” 
  &&  “ (INT_MIN < size) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
.

Definition mpz_abs_sub_partial_solve_wit_2 := mpz_abs_sub_partial_solve_wit_2_pure -> mpz_abs_sub_partial_solve_wit_2_aux.

Definition mpz_abs_sub_partial_solve_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval = (Zabs (size)))) (PreH2 : (same_sign n size )) (PreH3 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
|--
  EX (cap_2: Z)  (size_2: Z)  (ptr_2: Z) ,
  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
.

Definition mpz_abs_sub_partial_solve_wit_4_pure := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size_2: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size: Z) (cap_2: Z) (PreH1 : (same_sign m size )) (PreH2 : ((Zabs (size)) <= cap_2)) (PreH3 : (retval = (Zabs (size_2)))) (PreH4 : (same_sign n size_2 )) (PreH5 : ((Zabs (size_2)) <= cap)) ,
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |->_)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_2)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ (size <= INT_MAX) ” 
  &&  “ (INT_MIN < size) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size_2: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size: Z) (cap_2: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (cap <= INT_MAX)) (PreH3 : (size_2 <= INT_MAX)) (PreH4 : (cap_2 <= INT_MAX)) (PreH5 : (size <= INT_MAX)) (PreH6 : (retval >= INT_MIN)) (PreH7 : (cap >= INT_MIN)) (PreH8 : (size_2 >= INT_MIN)) (PreH9 : (cap_2 >= INT_MIN)) (PreH10 : (size >= INT_MIN)) (PreH11 : (same_sign m size )) (PreH12 : ((Zabs (size)) <= cap_2)) (PreH13 : (retval = (Zabs (size_2)))) (PreH14 : (same_sign n size_2 )) (PreH15 : ((Zabs (size_2)) <= cap)) ,
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |->_)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_2)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ (INT_MIN < size) ”
).

Definition mpz_abs_sub_partial_solve_wit_4_pure_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size_2: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size: Z) (cap_2: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (cap <= INT_MAX)) (PreH3 : (size_2 <= INT_MAX)) (PreH4 : (cap_2 <= INT_MAX)) (PreH5 : (size <= INT_MAX)) (PreH6 : (retval >= INT_MIN)) (PreH7 : (cap >= INT_MIN)) (PreH8 : (size_2 >= INT_MIN)) (PreH9 : (cap_2 >= INT_MIN)) (PreH10 : (size >= INT_MIN)) (PreH11 : (same_sign m size )) (PreH12 : ((Zabs (size)) <= cap_2)) (PreH13 : (retval = (Zabs (size_2)))) (PreH14 : (same_sign n size_2 )) (PreH15 : ((Zabs (size_2)) <= cap)) ,
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |->_)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_2)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ (INT_MIN < size) ”
.

Definition mpz_abs_sub_partial_solve_wit_4_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size_2: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size: Z) (cap_2: Z) (PreH1 : (same_sign m size )) (PreH2 : ((Zabs (size)) <= cap_2)) (PreH3 : (retval = (Zabs (size_2)))) (PreH4 : (same_sign n size_2 )) (PreH5 : ((Zabs (size_2)) <= cap)) ,
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_2)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
|--
  “ (size <= INT_MAX) ” 
  &&  “ (INT_MIN < size) ” 
  &&  “ (same_sign m size ) ” 
  &&  “ ((Zabs (size)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size_2))) ” 
  &&  “ (same_sign n size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_2)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
.

Definition mpz_abs_sub_partial_solve_wit_4 := mpz_abs_sub_partial_solve_wit_4_pure -> mpz_abs_sub_partial_solve_wit_4_aux.

Definition mpz_abs_sub_partial_solve_wit_5_pure := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (size_2)))) (PreH2 : (same_sign m size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (same_sign n size )) (PreH6 : ((Zabs (size)) <= cap)) ,
  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |->_)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ (retval >= 0) ” 
  &&  “ (retval_2 >= 0) ” 
  &&  “ ((Zabs (size_2)) >= 0) ” 
  &&  “ ((Zabs (size)) >= 0) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (cap <= INT_MAX)) (PreH3 : (size <= INT_MAX)) (PreH4 : (retval_2 <= INT_MAX)) (PreH5 : (cap_2 <= INT_MAX)) (PreH6 : (size_2 <= INT_MAX)) (PreH7 : (retval >= INT_MIN)) (PreH8 : (cap >= INT_MIN)) (PreH9 : (size >= INT_MIN)) (PreH10 : (retval_2 >= INT_MIN)) (PreH11 : (cap_2 >= INT_MIN)) (PreH12 : (size_2 >= INT_MIN)) (PreH13 : (retval_2 = (Zabs (size_2)))) (PreH14 : (same_sign m size_2 )) (PreH15 : ((Zabs (size_2)) <= cap_2)) (PreH16 : (retval = (Zabs (size)))) (PreH17 : (same_sign n size )) (PreH18 : ((Zabs (size)) <= cap)) ,
  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |->_)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ ((Zabs (size)) >= 0) ” 
  &&  “ ((Zabs (size_2)) >= 0) ” 
  &&  “ (retval_2 >= 0) ” 
  &&  “ (retval >= 0) ”
).

Definition mpz_abs_sub_partial_solve_wit_5_pure_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (cap <= INT_MAX)) (PreH3 : (size <= INT_MAX)) (PreH4 : (retval_2 <= INT_MAX)) (PreH5 : (cap_2 <= INT_MAX)) (PreH6 : (size_2 <= INT_MAX)) (PreH7 : (retval >= INT_MIN)) (PreH8 : (cap >= INT_MIN)) (PreH9 : (size >= INT_MIN)) (PreH10 : (retval_2 >= INT_MIN)) (PreH11 : (cap_2 >= INT_MIN)) (PreH12 : (size_2 >= INT_MIN)) (PreH13 : (retval_2 = (Zabs (size_2)))) (PreH14 : (same_sign m size_2 )) (PreH15 : ((Zabs (size_2)) <= cap_2)) (PreH16 : (retval = (Zabs (size)))) (PreH17 : (same_sign n size )) (PreH18 : ((Zabs (size)) <= cap)) ,
  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |->_)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ ((Zabs (size)) >= 0) ”
.

Definition mpz_abs_sub_partial_solve_wit_5_pure_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (cap <= INT_MAX)) (PreH3 : (size <= INT_MAX)) (PreH4 : (retval_2 <= INT_MAX)) (PreH5 : (cap_2 <= INT_MAX)) (PreH6 : (size_2 <= INT_MAX)) (PreH7 : (retval >= INT_MIN)) (PreH8 : (cap >= INT_MIN)) (PreH9 : (size >= INT_MIN)) (PreH10 : (retval_2 >= INT_MIN)) (PreH11 : (cap_2 >= INT_MIN)) (PreH12 : (size_2 >= INT_MIN)) (PreH13 : (retval_2 = (Zabs (size_2)))) (PreH14 : (same_sign m size_2 )) (PreH15 : ((Zabs (size_2)) <= cap_2)) (PreH16 : (retval = (Zabs (size)))) (PreH17 : (same_sign n size )) (PreH18 : ((Zabs (size)) <= cap)) ,
  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |->_)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ ((Zabs (size_2)) >= 0) ”
.

Definition mpz_abs_sub_partial_solve_wit_5_pure_split_goal_3 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (cap <= INT_MAX)) (PreH3 : (size <= INT_MAX)) (PreH4 : (retval_2 <= INT_MAX)) (PreH5 : (cap_2 <= INT_MAX)) (PreH6 : (size_2 <= INT_MAX)) (PreH7 : (retval >= INT_MIN)) (PreH8 : (cap >= INT_MIN)) (PreH9 : (size >= INT_MIN)) (PreH10 : (retval_2 >= INT_MIN)) (PreH11 : (cap_2 >= INT_MIN)) (PreH12 : (size_2 >= INT_MIN)) (PreH13 : (retval_2 = (Zabs (size_2)))) (PreH14 : (same_sign m size_2 )) (PreH15 : ((Zabs (size_2)) <= cap_2)) (PreH16 : (retval = (Zabs (size)))) (PreH17 : (same_sign n size )) (PreH18 : ((Zabs (size)) <= cap)) ,
  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |->_)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ (retval_2 >= 0) ”
.

Definition mpz_abs_sub_partial_solve_wit_5_pure_split_goal_4 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (cap <= INT_MAX)) (PreH3 : (size <= INT_MAX)) (PreH4 : (retval_2 <= INT_MAX)) (PreH5 : (cap_2 <= INT_MAX)) (PreH6 : (size_2 <= INT_MAX)) (PreH7 : (retval >= INT_MIN)) (PreH8 : (cap >= INT_MIN)) (PreH9 : (size >= INT_MIN)) (PreH10 : (retval_2 >= INT_MIN)) (PreH11 : (cap_2 >= INT_MIN)) (PreH12 : (size_2 >= INT_MIN)) (PreH13 : (retval_2 = (Zabs (size_2)))) (PreH14 : (same_sign m size_2 )) (PreH15 : ((Zabs (size_2)) <= cap_2)) (PreH16 : (retval = (Zabs (size)))) (PreH17 : (same_sign n size )) (PreH18 : ((Zabs (size)) <= cap)) ,
  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((( &( "cmp" ) )) # Int  |->_)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((( &( "bn" ) )) # Int  |-> retval_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "an" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ (retval >= 0) ”
.

Definition mpz_abs_sub_partial_solve_wit_5_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (size_2)))) (PreH2 : (same_sign m size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (same_sign n size )) (PreH6 : ((Zabs (size)) <= cap)) ,
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
|--
  “ (retval >= 0) ” 
  &&  “ (retval_2 >= 0) ” 
  &&  “ ((Zabs (size_2)) >= 0) ” 
  &&  “ ((Zabs (size)) >= 0) ” 
  &&  “ (retval_2 = (Zabs (size_2))) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) retval )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) retval_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
.

Definition mpz_abs_sub_partial_solve_wit_5 := mpz_abs_sub_partial_solve_wit_5_pure -> mpz_abs_sub_partial_solve_wit_5_aux.

Definition mpz_abs_sub_partial_solve_wit_6_pure := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rptr: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (PreH1 : (cmp > 0)) (PreH2 : ((Zabs (n)) > (Zabs (m)))) (PreH3 : (cmp = 1)) (PreH4 : (bn = (Zabs (b_pre__mp_size)))) (PreH5 : (same_sign m b_pre__mp_size )) (PreH6 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH7 : (an = (Zabs (a_pre__mp_size)))) (PreH8 : (same_sign n a_pre__mp_size )) (PreH9 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH10 : ((Zabs (rsize)) <= rcap)) (PreH11 : (same_sign l rsize )) (PreH12 : (rcap >= 0)) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (rcap >= 0) ” 
  &&  “ (an >= 1) ” 
  &&  “ (an <= INT_MAX) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= INT_MAX) ” 
  &&  “ ((Zabs (a_pre__mp_size)) >= 1) ” 
  &&  “ (rcap <= INT_MAX) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rptr: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (PreH1 : (rcap <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a_pre__mp_alloc <= INT_MAX)) (PreH4 : (a_pre__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b_pre__mp_alloc <= INT_MAX)) (PreH7 : (b_pre__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (rcap >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a_pre__mp_alloc >= INT_MIN)) (PreH13 : (a_pre__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b_pre__mp_alloc >= INT_MIN)) (PreH16 : (b_pre__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp > 0)) (PreH20 : ((Zabs (n)) > (Zabs (m)))) (PreH21 : (cmp = 1)) (PreH22 : (bn = (Zabs (b_pre__mp_size)))) (PreH23 : (same_sign m b_pre__mp_size )) (PreH24 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH25 : (an = (Zabs (a_pre__mp_size)))) (PreH26 : (same_sign n a_pre__mp_size )) (PreH27 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH28 : ((Zabs (rsize)) <= rcap)) (PreH29 : (same_sign l rsize )) (PreH30 : (rcap >= 0)) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ ((Zabs (a_pre__mp_size)) >= 1) ” 
  &&  “ (an >= 1) ”
).

Definition mpz_abs_sub_partial_solve_wit_6_pure_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rptr: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (PreH1 : (rcap <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a_pre__mp_alloc <= INT_MAX)) (PreH4 : (a_pre__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b_pre__mp_alloc <= INT_MAX)) (PreH7 : (b_pre__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (rcap >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a_pre__mp_alloc >= INT_MIN)) (PreH13 : (a_pre__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b_pre__mp_alloc >= INT_MIN)) (PreH16 : (b_pre__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp > 0)) (PreH20 : ((Zabs (n)) > (Zabs (m)))) (PreH21 : (cmp = 1)) (PreH22 : (bn = (Zabs (b_pre__mp_size)))) (PreH23 : (same_sign m b_pre__mp_size )) (PreH24 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH25 : (an = (Zabs (a_pre__mp_size)))) (PreH26 : (same_sign n a_pre__mp_size )) (PreH27 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH28 : ((Zabs (rsize)) <= rcap)) (PreH29 : (same_sign l rsize )) (PreH30 : (rcap >= 0)) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ ((Zabs (a_pre__mp_size)) >= 1) ”
.

Definition mpz_abs_sub_partial_solve_wit_6_pure_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rptr: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (PreH1 : (rcap <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a_pre__mp_alloc <= INT_MAX)) (PreH4 : (a_pre__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b_pre__mp_alloc <= INT_MAX)) (PreH7 : (b_pre__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (rcap >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a_pre__mp_alloc >= INT_MIN)) (PreH13 : (a_pre__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b_pre__mp_alloc >= INT_MIN)) (PreH16 : (b_pre__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp > 0)) (PreH20 : ((Zabs (n)) > (Zabs (m)))) (PreH21 : (cmp = 1)) (PreH22 : (bn = (Zabs (b_pre__mp_size)))) (PreH23 : (same_sign m b_pre__mp_size )) (PreH24 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH25 : (an = (Zabs (a_pre__mp_size)))) (PreH26 : (same_sign n a_pre__mp_size )) (PreH27 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH28 : ((Zabs (rsize)) <= rcap)) (PreH29 : (same_sign l rsize )) (PreH30 : (rcap >= 0)) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (an >= 1) ”
.

Definition mpz_abs_sub_partial_solve_wit_6_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rptr: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (PreH1 : (cmp > 0)) (PreH2 : ((Zabs (n)) > (Zabs (m)))) (PreH3 : (cmp = 1)) (PreH4 : (bn = (Zabs (b_pre__mp_size)))) (PreH5 : (same_sign m b_pre__mp_size )) (PreH6 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH7 : (an = (Zabs (a_pre__mp_size)))) (PreH8 : (same_sign n a_pre__mp_size )) (PreH9 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH10 : ((Zabs (rsize)) <= rcap)) (PreH11 : (same_sign l rsize )) (PreH12 : (rcap >= 0)) ,
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
|--
  “ (rcap >= 0) ” 
  &&  “ (an >= 1) ” 
  &&  “ (an <= INT_MAX) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= INT_MAX) ” 
  &&  “ ((Zabs (a_pre__mp_size)) >= 1) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ (cmp > 0) ” 
  &&  “ ((Zabs (n)) > (Zabs (m))) ” 
  &&  “ (cmp = 1) ” 
  &&  “ (bn = (Zabs (b_pre__mp_size))) ” 
  &&  “ (same_sign m b_pre__mp_size ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc) ” 
  &&  “ (an = (Zabs (a_pre__mp_size))) ” 
  &&  “ (same_sign n a_pre__mp_size ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ (rcap >= 0) ”
  &&  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
.

Definition mpz_abs_sub_partial_solve_wit_6 := mpz_abs_sub_partial_solve_wit_6_pure -> mpz_abs_sub_partial_solve_wit_6_aux.

Definition mpz_abs_sub_partial_solve_wit_7_pure := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (PreH1 : (cmp > 0)) (PreH2 : ((Zabs (n)) > (Zabs (m)))) (PreH3 : (cmp = 1)) (PreH4 : (bn = (Zabs (b_pre__mp_size)))) (PreH5 : (same_sign m b_pre__mp_size )) (PreH6 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH7 : (an = (Zabs (a_pre__mp_size)))) (PreH8 : (same_sign n a_pre__mp_size )) (PreH9 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH10 : (same_sign l rsize )) (PreH11 : ((Zabs (rsize)) <= rcap)) (PreH12 : (rcap >= 0)) (PreH13 : (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap)))) (PreH14 : (r__mp_d = rp)) (PreH15 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH16 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_full rp an )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
|--
  “ (an >= bn) ” 
  &&  “ (an > 0) ” 
  &&  “ (bn >= 0) ” 
  &&  “ ((Zabs (b_pre__mp_size)) >= 0) ” 
  &&  “ ((Zabs (a_pre__mp_size)) > 0) ” 
  &&  “ ((Zabs (a_pre__mp_size)) >= (Zabs (b_pre__mp_size))) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a_pre__mp_alloc <= INT_MAX)) (PreH4 : (a_pre__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b_pre__mp_alloc <= INT_MAX)) (PreH7 : (b_pre__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (r__mp_alloc >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a_pre__mp_alloc >= INT_MIN)) (PreH13 : (a_pre__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b_pre__mp_alloc >= INT_MIN)) (PreH16 : (b_pre__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp > 0)) (PreH20 : ((Zabs (n)) > (Zabs (m)))) (PreH21 : (cmp = 1)) (PreH22 : (bn = (Zabs (b_pre__mp_size)))) (PreH23 : (same_sign m b_pre__mp_size )) (PreH24 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH25 : (an = (Zabs (a_pre__mp_size)))) (PreH26 : (same_sign n a_pre__mp_size )) (PreH27 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH28 : (same_sign l rsize )) (PreH29 : ((Zabs (rsize)) <= rcap)) (PreH30 : (rcap >= 0)) (PreH31 : (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap)))) (PreH32 : (r__mp_d = rp)) (PreH33 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH34 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_full rp an )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
|--
  “ ((Zabs (a_pre__mp_size)) >= (Zabs (b_pre__mp_size))) ” 
  &&  “ ((Zabs (a_pre__mp_size)) > 0) ” 
  &&  “ ((Zabs (b_pre__mp_size)) >= 0) ” 
  &&  “ (bn >= 0) ” 
  &&  “ (an > 0) ” 
  &&  “ (an >= bn) ”
).

Definition mpz_abs_sub_partial_solve_wit_7_pure_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a_pre__mp_alloc <= INT_MAX)) (PreH4 : (a_pre__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b_pre__mp_alloc <= INT_MAX)) (PreH7 : (b_pre__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (r__mp_alloc >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a_pre__mp_alloc >= INT_MIN)) (PreH13 : (a_pre__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b_pre__mp_alloc >= INT_MIN)) (PreH16 : (b_pre__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp > 0)) (PreH20 : ((Zabs (n)) > (Zabs (m)))) (PreH21 : (cmp = 1)) (PreH22 : (bn = (Zabs (b_pre__mp_size)))) (PreH23 : (same_sign m b_pre__mp_size )) (PreH24 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH25 : (an = (Zabs (a_pre__mp_size)))) (PreH26 : (same_sign n a_pre__mp_size )) (PreH27 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH28 : (same_sign l rsize )) (PreH29 : ((Zabs (rsize)) <= rcap)) (PreH30 : (rcap >= 0)) (PreH31 : (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap)))) (PreH32 : (r__mp_d = rp)) (PreH33 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH34 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_full rp an )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
|--
  “ ((Zabs (a_pre__mp_size)) >= (Zabs (b_pre__mp_size))) ”
.

Definition mpz_abs_sub_partial_solve_wit_7_pure_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a_pre__mp_alloc <= INT_MAX)) (PreH4 : (a_pre__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b_pre__mp_alloc <= INT_MAX)) (PreH7 : (b_pre__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (r__mp_alloc >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a_pre__mp_alloc >= INT_MIN)) (PreH13 : (a_pre__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b_pre__mp_alloc >= INT_MIN)) (PreH16 : (b_pre__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp > 0)) (PreH20 : ((Zabs (n)) > (Zabs (m)))) (PreH21 : (cmp = 1)) (PreH22 : (bn = (Zabs (b_pre__mp_size)))) (PreH23 : (same_sign m b_pre__mp_size )) (PreH24 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH25 : (an = (Zabs (a_pre__mp_size)))) (PreH26 : (same_sign n a_pre__mp_size )) (PreH27 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH28 : (same_sign l rsize )) (PreH29 : ((Zabs (rsize)) <= rcap)) (PreH30 : (rcap >= 0)) (PreH31 : (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap)))) (PreH32 : (r__mp_d = rp)) (PreH33 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH34 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_full rp an )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
|--
  “ ((Zabs (a_pre__mp_size)) > 0) ”
.

Definition mpz_abs_sub_partial_solve_wit_7_pure_split_goal_3 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a_pre__mp_alloc <= INT_MAX)) (PreH4 : (a_pre__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b_pre__mp_alloc <= INT_MAX)) (PreH7 : (b_pre__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (r__mp_alloc >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a_pre__mp_alloc >= INT_MIN)) (PreH13 : (a_pre__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b_pre__mp_alloc >= INT_MIN)) (PreH16 : (b_pre__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp > 0)) (PreH20 : ((Zabs (n)) > (Zabs (m)))) (PreH21 : (cmp = 1)) (PreH22 : (bn = (Zabs (b_pre__mp_size)))) (PreH23 : (same_sign m b_pre__mp_size )) (PreH24 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH25 : (an = (Zabs (a_pre__mp_size)))) (PreH26 : (same_sign n a_pre__mp_size )) (PreH27 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH28 : (same_sign l rsize )) (PreH29 : ((Zabs (rsize)) <= rcap)) (PreH30 : (rcap >= 0)) (PreH31 : (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap)))) (PreH32 : (r__mp_d = rp)) (PreH33 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH34 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_full rp an )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
|--
  “ ((Zabs (b_pre__mp_size)) >= 0) ”
.

Definition mpz_abs_sub_partial_solve_wit_7_pure_split_goal_4 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a_pre__mp_alloc <= INT_MAX)) (PreH4 : (a_pre__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b_pre__mp_alloc <= INT_MAX)) (PreH7 : (b_pre__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (r__mp_alloc >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a_pre__mp_alloc >= INT_MIN)) (PreH13 : (a_pre__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b_pre__mp_alloc >= INT_MIN)) (PreH16 : (b_pre__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp > 0)) (PreH20 : ((Zabs (n)) > (Zabs (m)))) (PreH21 : (cmp = 1)) (PreH22 : (bn = (Zabs (b_pre__mp_size)))) (PreH23 : (same_sign m b_pre__mp_size )) (PreH24 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH25 : (an = (Zabs (a_pre__mp_size)))) (PreH26 : (same_sign n a_pre__mp_size )) (PreH27 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH28 : (same_sign l rsize )) (PreH29 : ((Zabs (rsize)) <= rcap)) (PreH30 : (rcap >= 0)) (PreH31 : (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap)))) (PreH32 : (r__mp_d = rp)) (PreH33 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH34 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_full rp an )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
|--
  “ (bn >= 0) ”
.

Definition mpz_abs_sub_partial_solve_wit_7_pure_split_goal_5 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a_pre__mp_alloc <= INT_MAX)) (PreH4 : (a_pre__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b_pre__mp_alloc <= INT_MAX)) (PreH7 : (b_pre__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (r__mp_alloc >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a_pre__mp_alloc >= INT_MIN)) (PreH13 : (a_pre__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b_pre__mp_alloc >= INT_MIN)) (PreH16 : (b_pre__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp > 0)) (PreH20 : ((Zabs (n)) > (Zabs (m)))) (PreH21 : (cmp = 1)) (PreH22 : (bn = (Zabs (b_pre__mp_size)))) (PreH23 : (same_sign m b_pre__mp_size )) (PreH24 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH25 : (an = (Zabs (a_pre__mp_size)))) (PreH26 : (same_sign n a_pre__mp_size )) (PreH27 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH28 : (same_sign l rsize )) (PreH29 : ((Zabs (rsize)) <= rcap)) (PreH30 : (rcap >= 0)) (PreH31 : (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap)))) (PreH32 : (r__mp_d = rp)) (PreH33 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH34 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_full rp an )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
|--
  “ (an > 0) ”
.

Definition mpz_abs_sub_partial_solve_wit_7_pure_split_goal_6 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a_pre__mp_alloc <= INT_MAX)) (PreH4 : (a_pre__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b_pre__mp_alloc <= INT_MAX)) (PreH7 : (b_pre__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (r__mp_alloc >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a_pre__mp_alloc >= INT_MIN)) (PreH13 : (a_pre__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b_pre__mp_alloc >= INT_MIN)) (PreH16 : (b_pre__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp > 0)) (PreH20 : ((Zabs (n)) > (Zabs (m)))) (PreH21 : (cmp = 1)) (PreH22 : (bn = (Zabs (b_pre__mp_size)))) (PreH23 : (same_sign m b_pre__mp_size )) (PreH24 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH25 : (an = (Zabs (a_pre__mp_size)))) (PreH26 : (same_sign n a_pre__mp_size )) (PreH27 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH28 : (same_sign l rsize )) (PreH29 : ((Zabs (rsize)) <= rcap)) (PreH30 : (rcap >= 0)) (PreH31 : (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap)))) (PreH32 : (r__mp_d = rp)) (PreH33 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH34 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_full rp an )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
|--
  “ (an >= bn) ”
.

Definition mpz_abs_sub_partial_solve_wit_7_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (PreH1 : (cmp > 0)) (PreH2 : ((Zabs (n)) > (Zabs (m)))) (PreH3 : (cmp = 1)) (PreH4 : (bn = (Zabs (b_pre__mp_size)))) (PreH5 : (same_sign m b_pre__mp_size )) (PreH6 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH7 : (an = (Zabs (a_pre__mp_size)))) (PreH8 : (same_sign n a_pre__mp_size )) (PreH9 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH10 : (same_sign l rsize )) (PreH11 : ((Zabs (rsize)) <= rcap)) (PreH12 : (rcap >= 0)) (PreH13 : (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap)))) (PreH14 : (r__mp_d = rp)) (PreH15 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH16 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) ,
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  (UIntArray.undef_full rp an )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
|--
  “ (an >= bn) ” 
  &&  “ (an > 0) ” 
  &&  “ (bn >= 0) ” 
  &&  “ ((Zabs (b_pre__mp_size)) >= 0) ” 
  &&  “ ((Zabs (a_pre__mp_size)) > 0) ” 
  &&  “ ((Zabs (a_pre__mp_size)) >= (Zabs (b_pre__mp_size))) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (m)) bn ) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (n)) an ) ” 
  &&  “ (cmp > 0) ” 
  &&  “ ((Zabs (n)) > (Zabs (m))) ” 
  &&  “ (cmp = 1) ” 
  &&  “ (bn = (Zabs (b_pre__mp_size))) ” 
  &&  “ (same_sign m b_pre__mp_size ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc) ” 
  &&  “ (an = (Zabs (a_pre__mp_size))) ” 
  &&  “ (same_sign n a_pre__mp_size ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap))) ” 
  &&  “ (r__mp_d = rp) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) ) ” 
  &&  “ (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ”
  &&  (mpd_store_Z UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  (mpd_store_Z UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_full rp an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
.

Definition mpz_abs_sub_partial_solve_wit_7 := mpz_abs_sub_partial_solve_wit_7_pure -> mpz_abs_sub_partial_solve_wit_7_aux.

Definition mpz_abs_sub_partial_solve_wit_8_pure := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (val_r_out: Z) (retval: Z) (PreH1 : ((val_r_out - (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (n)) - (Zabs (m)) ))) (PreH2 : (is_compact_Z UINT_MOD (Zabs (m)) bn )) (PreH3 : (is_compact_Z UINT_MOD (Zabs (n)) an )) (PreH4 : (cmp > 0)) (PreH5 : ((Zabs (n)) > (Zabs (m)))) (PreH6 : (cmp = 1)) (PreH7 : (bn = (Zabs (b_pre__mp_size)))) (PreH8 : (same_sign m b_pre__mp_size )) (PreH9 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH10 : (an = (Zabs (a_pre__mp_size)))) (PreH11 : (same_sign n a_pre__mp_size )) (PreH12 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH13 : (same_sign l rsize )) (PreH14 : ((Zabs (rsize)) <= rcap)) (PreH15 : (rcap >= 0)) (PreH16 : (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap)))) (PreH17 : (r__mp_d = rp)) (PreH18 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH19 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) ,
  (mpd_store_Z UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  (mpd_store_Z UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (mpd_store_Z UINT_MOD rp val_r_out an )
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
|--
  “ (0 <= an) ” 
  &&  “ (0 <= (Zabs (a_pre__mp_size))) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (val_r_out: Z) (retval: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a_pre__mp_alloc <= INT_MAX)) (PreH4 : (a_pre__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b_pre__mp_alloc <= INT_MAX)) (PreH7 : (b_pre__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (r__mp_alloc >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a_pre__mp_alloc >= INT_MIN)) (PreH13 : (a_pre__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b_pre__mp_alloc >= INT_MIN)) (PreH16 : (b_pre__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : ((val_r_out - (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (n)) - (Zabs (m)) ))) (PreH20 : (is_compact_Z UINT_MOD (Zabs (m)) bn )) (PreH21 : (is_compact_Z UINT_MOD (Zabs (n)) an )) (PreH22 : (cmp > 0)) (PreH23 : ((Zabs (n)) > (Zabs (m)))) (PreH24 : (cmp = 1)) (PreH25 : (bn = (Zabs (b_pre__mp_size)))) (PreH26 : (same_sign m b_pre__mp_size )) (PreH27 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH28 : (an = (Zabs (a_pre__mp_size)))) (PreH29 : (same_sign n a_pre__mp_size )) (PreH30 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH31 : (same_sign l rsize )) (PreH32 : ((Zabs (rsize)) <= rcap)) (PreH33 : (rcap >= 0)) (PreH34 : (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap)))) (PreH35 : (r__mp_d = rp)) (PreH36 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH37 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) ,
  (mpd_store_Z UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  (mpd_store_Z UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (mpd_store_Z UINT_MOD rp val_r_out an )
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
|--
  “ (0 <= (Zabs (a_pre__mp_size))) ” 
  &&  “ (0 <= an) ”
).

Definition mpz_abs_sub_partial_solve_wit_8_pure_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (val_r_out: Z) (retval: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a_pre__mp_alloc <= INT_MAX)) (PreH4 : (a_pre__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b_pre__mp_alloc <= INT_MAX)) (PreH7 : (b_pre__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (r__mp_alloc >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a_pre__mp_alloc >= INT_MIN)) (PreH13 : (a_pre__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b_pre__mp_alloc >= INT_MIN)) (PreH16 : (b_pre__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : ((val_r_out - (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (n)) - (Zabs (m)) ))) (PreH20 : (is_compact_Z UINT_MOD (Zabs (m)) bn )) (PreH21 : (is_compact_Z UINT_MOD (Zabs (n)) an )) (PreH22 : (cmp > 0)) (PreH23 : ((Zabs (n)) > (Zabs (m)))) (PreH24 : (cmp = 1)) (PreH25 : (bn = (Zabs (b_pre__mp_size)))) (PreH26 : (same_sign m b_pre__mp_size )) (PreH27 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH28 : (an = (Zabs (a_pre__mp_size)))) (PreH29 : (same_sign n a_pre__mp_size )) (PreH30 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH31 : (same_sign l rsize )) (PreH32 : ((Zabs (rsize)) <= rcap)) (PreH33 : (rcap >= 0)) (PreH34 : (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap)))) (PreH35 : (r__mp_d = rp)) (PreH36 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH37 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) ,
  (mpd_store_Z UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  (mpd_store_Z UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (mpd_store_Z UINT_MOD rp val_r_out an )
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
|--
  “ (0 <= (Zabs (a_pre__mp_size))) ”
.

Definition mpz_abs_sub_partial_solve_wit_8_pure_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (val_r_out: Z) (retval: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a_pre__mp_alloc <= INT_MAX)) (PreH4 : (a_pre__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b_pre__mp_alloc <= INT_MAX)) (PreH7 : (b_pre__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (r__mp_alloc >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a_pre__mp_alloc >= INT_MIN)) (PreH13 : (a_pre__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b_pre__mp_alloc >= INT_MIN)) (PreH16 : (b_pre__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : ((val_r_out - (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (n)) - (Zabs (m)) ))) (PreH20 : (is_compact_Z UINT_MOD (Zabs (m)) bn )) (PreH21 : (is_compact_Z UINT_MOD (Zabs (n)) an )) (PreH22 : (cmp > 0)) (PreH23 : ((Zabs (n)) > (Zabs (m)))) (PreH24 : (cmp = 1)) (PreH25 : (bn = (Zabs (b_pre__mp_size)))) (PreH26 : (same_sign m b_pre__mp_size )) (PreH27 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH28 : (an = (Zabs (a_pre__mp_size)))) (PreH29 : (same_sign n a_pre__mp_size )) (PreH30 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH31 : (same_sign l rsize )) (PreH32 : ((Zabs (rsize)) <= rcap)) (PreH33 : (rcap >= 0)) (PreH34 : (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap)))) (PreH35 : (r__mp_d = rp)) (PreH36 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH37 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) ,
  (mpd_store_Z UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  (mpd_store_Z UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (mpd_store_Z UINT_MOD rp val_r_out an )
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
|--
  “ (0 <= an) ”
.

Definition mpz_abs_sub_partial_solve_wit_8_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (val_r_out: Z) (retval: Z) (PreH1 : ((val_r_out - (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (n)) - (Zabs (m)) ))) (PreH2 : (is_compact_Z UINT_MOD (Zabs (m)) bn )) (PreH3 : (is_compact_Z UINT_MOD (Zabs (n)) an )) (PreH4 : (cmp > 0)) (PreH5 : ((Zabs (n)) > (Zabs (m)))) (PreH6 : (cmp = 1)) (PreH7 : (bn = (Zabs (b_pre__mp_size)))) (PreH8 : (same_sign m b_pre__mp_size )) (PreH9 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH10 : (an = (Zabs (a_pre__mp_size)))) (PreH11 : (same_sign n a_pre__mp_size )) (PreH12 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH13 : (same_sign l rsize )) (PreH14 : ((Zabs (rsize)) <= rcap)) (PreH15 : (rcap >= 0)) (PreH16 : (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap)))) (PreH17 : (r__mp_d = rp)) (PreH18 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH19 : (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap)))) ,
  (mpd_store_Z UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  (mpd_store_Z UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (mpd_store_Z UINT_MOD rp val_r_out an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
|--
  “ (0 <= an) ” 
  &&  “ (0 <= (Zabs (a_pre__mp_size))) ” 
  &&  “ ((val_r_out - (retval * (Z.pow (UINT_MOD) (an)) ) ) = ((Zabs (n)) - (Zabs (m)) )) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (m)) bn ) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (n)) an ) ” 
  &&  “ (cmp > 0) ” 
  &&  “ ((Zabs (n)) > (Zabs (m))) ” 
  &&  “ (cmp = 1) ” 
  &&  “ (bn = (Zabs (b_pre__mp_size))) ” 
  &&  “ (same_sign m b_pre__mp_size ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc) ” 
  &&  “ (an = (Zabs (a_pre__mp_size))) ” 
  &&  “ (same_sign n a_pre__mp_size ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (r__mp_alloc = (Z.max ((Z.max (an) (1))) (rcap))) ” 
  &&  “ (r__mp_d = rp) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) ) ” 
  &&  “ (an < (Z.max ((Z.max ((an + 1 )) (1))) (rcap))) ”
  &&  (mpd_store_Z UINT_MOD rp val_r_out an )
  **  (mpd_store_Z UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  (mpd_store_Z UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  (UIntArray.undef_seg rp an (Z.max ((Z.max (an) (1))) (rcap)) )
.

Definition mpz_abs_sub_partial_solve_wit_8 := mpz_abs_sub_partial_solve_wit_8_pure -> mpz_abs_sub_partial_solve_wit_8_aux.

Definition mpz_abs_sub_partial_solve_wit_9_pure := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rptr: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (PreH1 : (cmp < 0)) (PreH2 : (cmp <= 0)) (PreH3 : ((Zabs (n)) < (Zabs (m)))) (PreH4 : (cmp = (-1))) (PreH5 : (bn = (Zabs (b_pre__mp_size)))) (PreH6 : (same_sign m b_pre__mp_size )) (PreH7 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH8 : (an = (Zabs (a_pre__mp_size)))) (PreH9 : (same_sign n a_pre__mp_size )) (PreH10 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH11 : ((Zabs (rsize)) <= rcap)) (PreH12 : (same_sign l rsize )) (PreH13 : (rcap >= 0)) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (rcap >= 0) ” 
  &&  “ (bn >= 1) ” 
  &&  “ (bn <= INT_MAX) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= INT_MAX) ” 
  &&  “ ((Zabs (b_pre__mp_size)) >= 1) ” 
  &&  “ (rcap <= INT_MAX) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rptr: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (PreH1 : (rcap <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a_pre__mp_alloc <= INT_MAX)) (PreH4 : (a_pre__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b_pre__mp_alloc <= INT_MAX)) (PreH7 : (b_pre__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (rcap >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a_pre__mp_alloc >= INT_MIN)) (PreH13 : (a_pre__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b_pre__mp_alloc >= INT_MIN)) (PreH16 : (b_pre__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp < 0)) (PreH20 : (cmp <= 0)) (PreH21 : ((Zabs (n)) < (Zabs (m)))) (PreH22 : (cmp = (-1))) (PreH23 : (bn = (Zabs (b_pre__mp_size)))) (PreH24 : (same_sign m b_pre__mp_size )) (PreH25 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH26 : (an = (Zabs (a_pre__mp_size)))) (PreH27 : (same_sign n a_pre__mp_size )) (PreH28 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH29 : ((Zabs (rsize)) <= rcap)) (PreH30 : (same_sign l rsize )) (PreH31 : (rcap >= 0)) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ ((Zabs (b_pre__mp_size)) >= 1) ” 
  &&  “ (bn >= 1) ”
).

Definition mpz_abs_sub_partial_solve_wit_9_pure_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rptr: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (PreH1 : (rcap <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a_pre__mp_alloc <= INT_MAX)) (PreH4 : (a_pre__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b_pre__mp_alloc <= INT_MAX)) (PreH7 : (b_pre__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (rcap >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a_pre__mp_alloc >= INT_MIN)) (PreH13 : (a_pre__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b_pre__mp_alloc >= INT_MIN)) (PreH16 : (b_pre__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp < 0)) (PreH20 : (cmp <= 0)) (PreH21 : ((Zabs (n)) < (Zabs (m)))) (PreH22 : (cmp = (-1))) (PreH23 : (bn = (Zabs (b_pre__mp_size)))) (PreH24 : (same_sign m b_pre__mp_size )) (PreH25 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH26 : (an = (Zabs (a_pre__mp_size)))) (PreH27 : (same_sign n a_pre__mp_size )) (PreH28 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH29 : ((Zabs (rsize)) <= rcap)) (PreH30 : (same_sign l rsize )) (PreH31 : (rcap >= 0)) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ ((Zabs (b_pre__mp_size)) >= 1) ”
.

Definition mpz_abs_sub_partial_solve_wit_9_pure_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rptr: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (PreH1 : (rcap <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a_pre__mp_alloc <= INT_MAX)) (PreH4 : (a_pre__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b_pre__mp_alloc <= INT_MAX)) (PreH7 : (b_pre__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (rcap >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a_pre__mp_alloc >= INT_MIN)) (PreH13 : (a_pre__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b_pre__mp_alloc >= INT_MIN)) (PreH16 : (b_pre__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp < 0)) (PreH20 : (cmp <= 0)) (PreH21 : ((Zabs (n)) < (Zabs (m)))) (PreH22 : (cmp = (-1))) (PreH23 : (bn = (Zabs (b_pre__mp_size)))) (PreH24 : (same_sign m b_pre__mp_size )) (PreH25 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH26 : (an = (Zabs (a_pre__mp_size)))) (PreH27 : (same_sign n a_pre__mp_size )) (PreH28 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH29 : ((Zabs (rsize)) <= rcap)) (PreH30 : (same_sign l rsize )) (PreH31 : (rcap >= 0)) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (bn >= 1) ”
.

Definition mpz_abs_sub_partial_solve_wit_9_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rptr: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (PreH1 : (cmp < 0)) (PreH2 : (cmp <= 0)) (PreH3 : ((Zabs (n)) < (Zabs (m)))) (PreH4 : (cmp = (-1))) (PreH5 : (bn = (Zabs (b_pre__mp_size)))) (PreH6 : (same_sign m b_pre__mp_size )) (PreH7 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH8 : (an = (Zabs (a_pre__mp_size)))) (PreH9 : (same_sign n a_pre__mp_size )) (PreH10 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH11 : ((Zabs (rsize)) <= rcap)) (PreH12 : (same_sign l rsize )) (PreH13 : (rcap >= 0)) ,
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
|--
  “ (rcap >= 0) ” 
  &&  “ (bn >= 1) ” 
  &&  “ (bn <= INT_MAX) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= INT_MAX) ” 
  &&  “ ((Zabs (b_pre__mp_size)) >= 1) ” 
  &&  “ (rcap <= INT_MAX) ” 
  &&  “ (cmp < 0) ” 
  &&  “ (cmp <= 0) ” 
  &&  “ ((Zabs (n)) < (Zabs (m))) ” 
  &&  “ (cmp = (-1)) ” 
  &&  “ (bn = (Zabs (b_pre__mp_size))) ” 
  &&  “ (same_sign m b_pre__mp_size ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc) ” 
  &&  “ (an = (Zabs (a_pre__mp_size))) ” 
  &&  “ (same_sign n a_pre__mp_size ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ (rcap >= 0) ”
  &&  (mpd_store_Z_compact UINT_MOD rptr (Zabs (l)) (Zabs (rsize)) )
  **  (UIntArray.undef_seg rptr (Zabs (rsize)) rcap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> rcap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> rptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
.

Definition mpz_abs_sub_partial_solve_wit_9 := mpz_abs_sub_partial_solve_wit_9_pure -> mpz_abs_sub_partial_solve_wit_9_aux.

Definition mpz_abs_sub_partial_solve_wit_10_pure := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (PreH1 : (cmp < 0)) (PreH2 : (cmp <= 0)) (PreH3 : ((Zabs (n)) < (Zabs (m)))) (PreH4 : (cmp = (-1))) (PreH5 : (bn = (Zabs (b_pre__mp_size)))) (PreH6 : (same_sign m b_pre__mp_size )) (PreH7 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH8 : (an = (Zabs (a_pre__mp_size)))) (PreH9 : (same_sign n a_pre__mp_size )) (PreH10 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH11 : (same_sign l rsize )) (PreH12 : ((Zabs (rsize)) <= rcap)) (PreH13 : (rcap >= 0)) (PreH14 : (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap)))) (PreH15 : (r__mp_d = rp)) (PreH16 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH17 : (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap)))) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_full rp bn )
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  “ (bn >= an) ” 
  &&  “ (bn > 0) ” 
  &&  “ (an >= 0) ” 
  &&  “ ((Zabs (a_pre__mp_size)) >= 0) ” 
  &&  “ ((Zabs (b_pre__mp_size)) > 0) ” 
  &&  “ ((Zabs (b_pre__mp_size)) >= (Zabs (a_pre__mp_size))) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a_pre__mp_alloc <= INT_MAX)) (PreH4 : (a_pre__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b_pre__mp_alloc <= INT_MAX)) (PreH7 : (b_pre__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (r__mp_alloc >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a_pre__mp_alloc >= INT_MIN)) (PreH13 : (a_pre__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b_pre__mp_alloc >= INT_MIN)) (PreH16 : (b_pre__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp < 0)) (PreH20 : (cmp <= 0)) (PreH21 : ((Zabs (n)) < (Zabs (m)))) (PreH22 : (cmp = (-1))) (PreH23 : (bn = (Zabs (b_pre__mp_size)))) (PreH24 : (same_sign m b_pre__mp_size )) (PreH25 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH26 : (an = (Zabs (a_pre__mp_size)))) (PreH27 : (same_sign n a_pre__mp_size )) (PreH28 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH29 : (same_sign l rsize )) (PreH30 : ((Zabs (rsize)) <= rcap)) (PreH31 : (rcap >= 0)) (PreH32 : (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap)))) (PreH33 : (r__mp_d = rp)) (PreH34 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH35 : (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap)))) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_full rp bn )
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  “ ((Zabs (b_pre__mp_size)) >= (Zabs (a_pre__mp_size))) ” 
  &&  “ ((Zabs (b_pre__mp_size)) > 0) ” 
  &&  “ ((Zabs (a_pre__mp_size)) >= 0) ” 
  &&  “ (an >= 0) ” 
  &&  “ (bn > 0) ” 
  &&  “ (bn >= an) ”
).

Definition mpz_abs_sub_partial_solve_wit_10_pure_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a_pre__mp_alloc <= INT_MAX)) (PreH4 : (a_pre__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b_pre__mp_alloc <= INT_MAX)) (PreH7 : (b_pre__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (r__mp_alloc >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a_pre__mp_alloc >= INT_MIN)) (PreH13 : (a_pre__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b_pre__mp_alloc >= INT_MIN)) (PreH16 : (b_pre__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp < 0)) (PreH20 : (cmp <= 0)) (PreH21 : ((Zabs (n)) < (Zabs (m)))) (PreH22 : (cmp = (-1))) (PreH23 : (bn = (Zabs (b_pre__mp_size)))) (PreH24 : (same_sign m b_pre__mp_size )) (PreH25 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH26 : (an = (Zabs (a_pre__mp_size)))) (PreH27 : (same_sign n a_pre__mp_size )) (PreH28 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH29 : (same_sign l rsize )) (PreH30 : ((Zabs (rsize)) <= rcap)) (PreH31 : (rcap >= 0)) (PreH32 : (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap)))) (PreH33 : (r__mp_d = rp)) (PreH34 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH35 : (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap)))) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_full rp bn )
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  “ ((Zabs (b_pre__mp_size)) >= (Zabs (a_pre__mp_size))) ”
.

Definition mpz_abs_sub_partial_solve_wit_10_pure_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a_pre__mp_alloc <= INT_MAX)) (PreH4 : (a_pre__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b_pre__mp_alloc <= INT_MAX)) (PreH7 : (b_pre__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (r__mp_alloc >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a_pre__mp_alloc >= INT_MIN)) (PreH13 : (a_pre__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b_pre__mp_alloc >= INT_MIN)) (PreH16 : (b_pre__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp < 0)) (PreH20 : (cmp <= 0)) (PreH21 : ((Zabs (n)) < (Zabs (m)))) (PreH22 : (cmp = (-1))) (PreH23 : (bn = (Zabs (b_pre__mp_size)))) (PreH24 : (same_sign m b_pre__mp_size )) (PreH25 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH26 : (an = (Zabs (a_pre__mp_size)))) (PreH27 : (same_sign n a_pre__mp_size )) (PreH28 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH29 : (same_sign l rsize )) (PreH30 : ((Zabs (rsize)) <= rcap)) (PreH31 : (rcap >= 0)) (PreH32 : (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap)))) (PreH33 : (r__mp_d = rp)) (PreH34 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH35 : (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap)))) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_full rp bn )
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  “ ((Zabs (b_pre__mp_size)) > 0) ”
.

Definition mpz_abs_sub_partial_solve_wit_10_pure_split_goal_3 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a_pre__mp_alloc <= INT_MAX)) (PreH4 : (a_pre__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b_pre__mp_alloc <= INT_MAX)) (PreH7 : (b_pre__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (r__mp_alloc >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a_pre__mp_alloc >= INT_MIN)) (PreH13 : (a_pre__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b_pre__mp_alloc >= INT_MIN)) (PreH16 : (b_pre__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp < 0)) (PreH20 : (cmp <= 0)) (PreH21 : ((Zabs (n)) < (Zabs (m)))) (PreH22 : (cmp = (-1))) (PreH23 : (bn = (Zabs (b_pre__mp_size)))) (PreH24 : (same_sign m b_pre__mp_size )) (PreH25 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH26 : (an = (Zabs (a_pre__mp_size)))) (PreH27 : (same_sign n a_pre__mp_size )) (PreH28 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH29 : (same_sign l rsize )) (PreH30 : ((Zabs (rsize)) <= rcap)) (PreH31 : (rcap >= 0)) (PreH32 : (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap)))) (PreH33 : (r__mp_d = rp)) (PreH34 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH35 : (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap)))) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_full rp bn )
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  “ ((Zabs (a_pre__mp_size)) >= 0) ”
.

Definition mpz_abs_sub_partial_solve_wit_10_pure_split_goal_4 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a_pre__mp_alloc <= INT_MAX)) (PreH4 : (a_pre__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b_pre__mp_alloc <= INT_MAX)) (PreH7 : (b_pre__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (r__mp_alloc >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a_pre__mp_alloc >= INT_MIN)) (PreH13 : (a_pre__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b_pre__mp_alloc >= INT_MIN)) (PreH16 : (b_pre__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp < 0)) (PreH20 : (cmp <= 0)) (PreH21 : ((Zabs (n)) < (Zabs (m)))) (PreH22 : (cmp = (-1))) (PreH23 : (bn = (Zabs (b_pre__mp_size)))) (PreH24 : (same_sign m b_pre__mp_size )) (PreH25 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH26 : (an = (Zabs (a_pre__mp_size)))) (PreH27 : (same_sign n a_pre__mp_size )) (PreH28 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH29 : (same_sign l rsize )) (PreH30 : ((Zabs (rsize)) <= rcap)) (PreH31 : (rcap >= 0)) (PreH32 : (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap)))) (PreH33 : (r__mp_d = rp)) (PreH34 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH35 : (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap)))) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_full rp bn )
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  “ (an >= 0) ”
.

Definition mpz_abs_sub_partial_solve_wit_10_pure_split_goal_5 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a_pre__mp_alloc <= INT_MAX)) (PreH4 : (a_pre__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b_pre__mp_alloc <= INT_MAX)) (PreH7 : (b_pre__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (r__mp_alloc >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a_pre__mp_alloc >= INT_MIN)) (PreH13 : (a_pre__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b_pre__mp_alloc >= INT_MIN)) (PreH16 : (b_pre__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp < 0)) (PreH20 : (cmp <= 0)) (PreH21 : ((Zabs (n)) < (Zabs (m)))) (PreH22 : (cmp = (-1))) (PreH23 : (bn = (Zabs (b_pre__mp_size)))) (PreH24 : (same_sign m b_pre__mp_size )) (PreH25 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH26 : (an = (Zabs (a_pre__mp_size)))) (PreH27 : (same_sign n a_pre__mp_size )) (PreH28 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH29 : (same_sign l rsize )) (PreH30 : ((Zabs (rsize)) <= rcap)) (PreH31 : (rcap >= 0)) (PreH32 : (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap)))) (PreH33 : (r__mp_d = rp)) (PreH34 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH35 : (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap)))) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_full rp bn )
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  “ (bn > 0) ”
.

Definition mpz_abs_sub_partial_solve_wit_10_pure_split_goal_6 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a_pre__mp_alloc <= INT_MAX)) (PreH4 : (a_pre__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b_pre__mp_alloc <= INT_MAX)) (PreH7 : (b_pre__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (r__mp_alloc >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a_pre__mp_alloc >= INT_MIN)) (PreH13 : (a_pre__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b_pre__mp_alloc >= INT_MIN)) (PreH16 : (b_pre__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : (cmp < 0)) (PreH20 : (cmp <= 0)) (PreH21 : ((Zabs (n)) < (Zabs (m)))) (PreH22 : (cmp = (-1))) (PreH23 : (bn = (Zabs (b_pre__mp_size)))) (PreH24 : (same_sign m b_pre__mp_size )) (PreH25 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH26 : (an = (Zabs (a_pre__mp_size)))) (PreH27 : (same_sign n a_pre__mp_size )) (PreH28 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH29 : (same_sign l rsize )) (PreH30 : ((Zabs (rsize)) <= rcap)) (PreH31 : (rcap >= 0)) (PreH32 : (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap)))) (PreH33 : (r__mp_d = rp)) (PreH34 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH35 : (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap)))) ,
  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_full rp bn )
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  “ (bn >= an) ”
.

Definition mpz_abs_sub_partial_solve_wit_10_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (PreH1 : (cmp < 0)) (PreH2 : (cmp <= 0)) (PreH3 : ((Zabs (n)) < (Zabs (m)))) (PreH4 : (cmp = (-1))) (PreH5 : (bn = (Zabs (b_pre__mp_size)))) (PreH6 : (same_sign m b_pre__mp_size )) (PreH7 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH8 : (an = (Zabs (a_pre__mp_size)))) (PreH9 : (same_sign n a_pre__mp_size )) (PreH10 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH11 : (same_sign l rsize )) (PreH12 : ((Zabs (rsize)) <= rcap)) (PreH13 : (rcap >= 0)) (PreH14 : (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap)))) (PreH15 : (r__mp_d = rp)) (PreH16 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH17 : (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap)))) ,
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (mpd_store_Z_compact UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  (UIntArray.undef_full rp bn )
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  “ (bn >= an) ” 
  &&  “ (bn > 0) ” 
  &&  “ (an >= 0) ” 
  &&  “ ((Zabs (a_pre__mp_size)) >= 0) ” 
  &&  “ ((Zabs (b_pre__mp_size)) > 0) ” 
  &&  “ ((Zabs (b_pre__mp_size)) >= (Zabs (a_pre__mp_size))) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (m)) bn ) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (n)) an ) ” 
  &&  “ (cmp < 0) ” 
  &&  “ (cmp <= 0) ” 
  &&  “ ((Zabs (n)) < (Zabs (m))) ” 
  &&  “ (cmp = (-1)) ” 
  &&  “ (bn = (Zabs (b_pre__mp_size))) ” 
  &&  “ (same_sign m b_pre__mp_size ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc) ” 
  &&  “ (an = (Zabs (a_pre__mp_size))) ” 
  &&  “ (same_sign n a_pre__mp_size ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap))) ” 
  &&  “ (r__mp_d = rp) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) ) ” 
  &&  “ (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap))) ”
  &&  (mpd_store_Z UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (mpd_store_Z UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  (UIntArray.undef_full rp bn )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
.

Definition mpz_abs_sub_partial_solve_wit_10 := mpz_abs_sub_partial_solve_wit_10_pure -> mpz_abs_sub_partial_solve_wit_10_aux.

Definition mpz_abs_sub_partial_solve_wit_11_pure := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (val_r_out: Z) (retval: Z) (PreH1 : ((val_r_out - (retval * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (m)) - (Zabs (n)) ))) (PreH2 : (is_compact_Z UINT_MOD (Zabs (m)) bn )) (PreH3 : (is_compact_Z UINT_MOD (Zabs (n)) an )) (PreH4 : (cmp < 0)) (PreH5 : (cmp <= 0)) (PreH6 : ((Zabs (n)) < (Zabs (m)))) (PreH7 : (cmp = (-1))) (PreH8 : (bn = (Zabs (b_pre__mp_size)))) (PreH9 : (same_sign m b_pre__mp_size )) (PreH10 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH11 : (an = (Zabs (a_pre__mp_size)))) (PreH12 : (same_sign n a_pre__mp_size )) (PreH13 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH14 : (same_sign l rsize )) (PreH15 : ((Zabs (rsize)) <= rcap)) (PreH16 : (rcap >= 0)) (PreH17 : (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap)))) (PreH18 : (r__mp_d = rp)) (PreH19 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH20 : (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap)))) ,
  (mpd_store_Z UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (mpd_store_Z UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  (mpd_store_Z UINT_MOD rp val_r_out bn )
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  “ (0 <= bn) ” 
  &&  “ (0 <= (Zabs (b_pre__mp_size))) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (val_r_out: Z) (retval: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a_pre__mp_alloc <= INT_MAX)) (PreH4 : (a_pre__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b_pre__mp_alloc <= INT_MAX)) (PreH7 : (b_pre__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (r__mp_alloc >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a_pre__mp_alloc >= INT_MIN)) (PreH13 : (a_pre__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b_pre__mp_alloc >= INT_MIN)) (PreH16 : (b_pre__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : ((val_r_out - (retval * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (m)) - (Zabs (n)) ))) (PreH20 : (is_compact_Z UINT_MOD (Zabs (m)) bn )) (PreH21 : (is_compact_Z UINT_MOD (Zabs (n)) an )) (PreH22 : (cmp < 0)) (PreH23 : (cmp <= 0)) (PreH24 : ((Zabs (n)) < (Zabs (m)))) (PreH25 : (cmp = (-1))) (PreH26 : (bn = (Zabs (b_pre__mp_size)))) (PreH27 : (same_sign m b_pre__mp_size )) (PreH28 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH29 : (an = (Zabs (a_pre__mp_size)))) (PreH30 : (same_sign n a_pre__mp_size )) (PreH31 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH32 : (same_sign l rsize )) (PreH33 : ((Zabs (rsize)) <= rcap)) (PreH34 : (rcap >= 0)) (PreH35 : (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap)))) (PreH36 : (r__mp_d = rp)) (PreH37 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH38 : (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap)))) ,
  (mpd_store_Z UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (mpd_store_Z UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  (mpd_store_Z UINT_MOD rp val_r_out bn )
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  “ (0 <= (Zabs (b_pre__mp_size))) ” 
  &&  “ (0 <= bn) ”
).

Definition mpz_abs_sub_partial_solve_wit_11_pure_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (val_r_out: Z) (retval: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a_pre__mp_alloc <= INT_MAX)) (PreH4 : (a_pre__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b_pre__mp_alloc <= INT_MAX)) (PreH7 : (b_pre__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (r__mp_alloc >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a_pre__mp_alloc >= INT_MIN)) (PreH13 : (a_pre__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b_pre__mp_alloc >= INT_MIN)) (PreH16 : (b_pre__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : ((val_r_out - (retval * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (m)) - (Zabs (n)) ))) (PreH20 : (is_compact_Z UINT_MOD (Zabs (m)) bn )) (PreH21 : (is_compact_Z UINT_MOD (Zabs (n)) an )) (PreH22 : (cmp < 0)) (PreH23 : (cmp <= 0)) (PreH24 : ((Zabs (n)) < (Zabs (m)))) (PreH25 : (cmp = (-1))) (PreH26 : (bn = (Zabs (b_pre__mp_size)))) (PreH27 : (same_sign m b_pre__mp_size )) (PreH28 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH29 : (an = (Zabs (a_pre__mp_size)))) (PreH30 : (same_sign n a_pre__mp_size )) (PreH31 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH32 : (same_sign l rsize )) (PreH33 : ((Zabs (rsize)) <= rcap)) (PreH34 : (rcap >= 0)) (PreH35 : (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap)))) (PreH36 : (r__mp_d = rp)) (PreH37 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH38 : (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap)))) ,
  (mpd_store_Z UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (mpd_store_Z UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  (mpd_store_Z UINT_MOD rp val_r_out bn )
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  “ (0 <= (Zabs (b_pre__mp_size))) ”
.

Definition mpz_abs_sub_partial_solve_wit_11_pure_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (val_r_out: Z) (retval: Z) (PreH1 : (r__mp_alloc <= INT_MAX)) (PreH2 : (rsize <= INT_MAX)) (PreH3 : (a_pre__mp_alloc <= INT_MAX)) (PreH4 : (a_pre__mp_size <= INT_MAX)) (PreH5 : (an <= INT_MAX)) (PreH6 : (b_pre__mp_alloc <= INT_MAX)) (PreH7 : (b_pre__mp_size <= INT_MAX)) (PreH8 : (bn <= INT_MAX)) (PreH9 : (cmp <= INT_MAX)) (PreH10 : (r__mp_alloc >= INT_MIN)) (PreH11 : (rsize >= INT_MIN)) (PreH12 : (a_pre__mp_alloc >= INT_MIN)) (PreH13 : (a_pre__mp_size >= INT_MIN)) (PreH14 : (an >= INT_MIN)) (PreH15 : (b_pre__mp_alloc >= INT_MIN)) (PreH16 : (b_pre__mp_size >= INT_MIN)) (PreH17 : (bn >= INT_MIN)) (PreH18 : (cmp >= INT_MIN)) (PreH19 : ((val_r_out - (retval * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (m)) - (Zabs (n)) ))) (PreH20 : (is_compact_Z UINT_MOD (Zabs (m)) bn )) (PreH21 : (is_compact_Z UINT_MOD (Zabs (n)) an )) (PreH22 : (cmp < 0)) (PreH23 : (cmp <= 0)) (PreH24 : ((Zabs (n)) < (Zabs (m)))) (PreH25 : (cmp = (-1))) (PreH26 : (bn = (Zabs (b_pre__mp_size)))) (PreH27 : (same_sign m b_pre__mp_size )) (PreH28 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH29 : (an = (Zabs (a_pre__mp_size)))) (PreH30 : (same_sign n a_pre__mp_size )) (PreH31 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH32 : (same_sign l rsize )) (PreH33 : ((Zabs (rsize)) <= rcap)) (PreH34 : (rcap >= 0)) (PreH35 : (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap)))) (PreH36 : (r__mp_d = rp)) (PreH37 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH38 : (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap)))) ,
  (mpd_store_Z UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (mpd_store_Z UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  (mpd_store_Z UINT_MOD rp val_r_out bn )
  **  ((( &( "cmp" ) )) # Int  |-> cmp)
  **  ((( &( "bn" ) )) # Int  |-> bn)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((( &( "an" ) )) # Int  |-> an)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  “ (0 <= bn) ”
.

Definition mpz_abs_sub_partial_solve_wit_11_aux := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (rsize: Z) (rcap: Z) (cmp: Z) (bn: Z) (b_pre__mp_size: Z) (b_pre__mp_alloc: Z) (an: Z) (a_pre__mp_size: Z) (a_pre__mp_alloc: Z) (r__mp_alloc: Z) (r__mp_d: Z) (rp: Z) (a_pre__mp_d: Z) (b_pre__mp_d: Z) (val_r_out: Z) (retval: Z) (PreH1 : ((val_r_out - (retval * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (m)) - (Zabs (n)) ))) (PreH2 : (is_compact_Z UINT_MOD (Zabs (m)) bn )) (PreH3 : (is_compact_Z UINT_MOD (Zabs (n)) an )) (PreH4 : (cmp < 0)) (PreH5 : (cmp <= 0)) (PreH6 : ((Zabs (n)) < (Zabs (m)))) (PreH7 : (cmp = (-1))) (PreH8 : (bn = (Zabs (b_pre__mp_size)))) (PreH9 : (same_sign m b_pre__mp_size )) (PreH10 : ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc)) (PreH11 : (an = (Zabs (a_pre__mp_size)))) (PreH12 : (same_sign n a_pre__mp_size )) (PreH13 : ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc)) (PreH14 : (same_sign l rsize )) (PreH15 : ((Zabs (rsize)) <= rcap)) (PreH16 : (rcap >= 0)) (PreH17 : (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap)))) (PreH18 : (r__mp_d = rp)) (PreH19 : (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) )) (PreH20 : (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap)))) ,
  (mpd_store_Z UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (mpd_store_Z UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  (mpd_store_Z UINT_MOD rp val_r_out bn )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
|--
  “ (0 <= bn) ” 
  &&  “ (0 <= (Zabs (b_pre__mp_size))) ” 
  &&  “ ((val_r_out - (retval * (Z.pow (UINT_MOD) (bn)) ) ) = ((Zabs (m)) - (Zabs (n)) )) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (m)) bn ) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (n)) an ) ” 
  &&  “ (cmp < 0) ” 
  &&  “ (cmp <= 0) ” 
  &&  “ ((Zabs (n)) < (Zabs (m))) ” 
  &&  “ (cmp = (-1)) ” 
  &&  “ (bn = (Zabs (b_pre__mp_size))) ” 
  &&  “ (same_sign m b_pre__mp_size ) ” 
  &&  “ ((Zabs (b_pre__mp_size)) <= b_pre__mp_alloc) ” 
  &&  “ (an = (Zabs (a_pre__mp_size))) ” 
  &&  “ (same_sign n a_pre__mp_size ) ” 
  &&  “ ((Zabs (a_pre__mp_size)) <= a_pre__mp_alloc) ” 
  &&  “ (same_sign l rsize ) ” 
  &&  “ ((Zabs (rsize)) <= rcap) ” 
  &&  “ (rcap >= 0) ” 
  &&  “ (r__mp_alloc = (Z.max ((Z.max (bn) (1))) (rcap))) ” 
  &&  “ (r__mp_d = rp) ” 
  &&  “ (is_compact_Z UINT_MOD (Zabs (l)) (Zabs (rsize)) ) ” 
  &&  “ (bn < (Z.max ((Z.max ((bn + 1 )) (1))) (rcap))) ”
  &&  (mpd_store_Z UINT_MOD rp val_r_out bn )
  **  (mpd_store_Z UINT_MOD b_pre__mp_d (Zabs (m)) bn )
  **  (mpd_store_Z UINT_MOD a_pre__mp_d (Zabs (n)) an )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> b_pre__mp_size)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> b_pre__mp_alloc)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> a_pre__mp_size)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> a_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rsize)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> r__mp_d)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> a_pre__mp_d)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> b_pre__mp_d)
  **  (UIntArray.undef_seg b_pre__mp_d (Zabs (b_pre__mp_size)) b_pre__mp_alloc )
  **  (UIntArray.undef_seg a_pre__mp_d (Zabs (a_pre__mp_size)) a_pre__mp_alloc )
  **  (UIntArray.undef_seg rp bn (Z.max ((Z.max (bn) (1))) (rcap)) )
.

Definition mpz_abs_sub_partial_solve_wit_11 := mpz_abs_sub_partial_solve_wit_11_pure -> mpz_abs_sub_partial_solve_wit_11_aux.

(*----- Function mpz_add -----*)

Definition mpz_add_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign m size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign n size )) (PreH4 : ((Zabs (size)) <= cap)) ,
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_add_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign n size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : ((Z.lxor size size_2) >= 0)) (PreH4 : (same_sign m size_2 )) (PreH5 : ((Zabs (size_2)) <= cap_2)) (PreH6 : (same_sign n size )) (PreH7 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) + (Zabs (m)) ) retval )
  **  ((( &( "rn" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_add_safety_wit_3 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 < 0)) (PreH2 : (same_sign n size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : ((Z.lxor size size_2) >= 0)) (PreH5 : (same_sign m size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign n size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) + (Zabs (m)) ) retval )
  **  ((( &( "rn" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (retval <> (INT_MIN)) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 < 0)) (PreH2 : (same_sign n size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : ((Z.lxor size size_2) >= 0)) (PreH5 : (same_sign m size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign n size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) + (Zabs (m)) ) retval )
  **  ((( &( "rn" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (retval <> (INT_MIN)) ”
).

Definition mpz_add_safety_wit_3_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 < 0)) (PreH2 : (same_sign n size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : ((Z.lxor size size_2) >= 0)) (PreH5 : (same_sign m size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign n size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) + (Zabs (m)) ) retval )
  **  ((( &( "rn" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (retval <> (INT_MIN)) ”
.

Definition mpz_add_safety_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign n size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : ((Z.lxor size size_2) < 0)) (PreH4 : (same_sign m size_2 )) (PreH5 : ((Zabs (size_2)) <= cap_2)) (PreH6 : (same_sign n size )) (PreH7 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) retval )
  **  ((( &( "rn" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_add_safety_wit_5 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 < 0)) (PreH2 : (same_sign n size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : ((Z.lxor size size_2) < 0)) (PreH5 : (same_sign m size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign n size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) retval )
  **  ((( &( "rn" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (retval <> (INT_MIN)) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 < 0)) (PreH2 : (same_sign n size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : ((Z.lxor size size_2) < 0)) (PreH5 : (same_sign m size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign n size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) retval )
  **  ((( &( "rn" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (retval <> (INT_MIN)) ”
).

Definition mpz_add_safety_wit_5_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 < 0)) (PreH2 : (same_sign n size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : ((Z.lxor size size_2) < 0)) (PreH5 : (same_sign m size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign n size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) retval )
  **  ((( &( "rn" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (retval <> (INT_MIN)) ”
.

Definition mpz_add_return_wit_1 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) + (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 >= 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) >= 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> retval)
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) + (Zabs (m)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
|--
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z r_pre (n + m ) )
) \/
(
forall (b_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) + (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 >= 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) >= 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) + (Zabs (m)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
|--
  “ (same_sign (n + m ) retval ) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs ((n + m ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
).

Definition mpz_add_return_wit_1_split_goal_1 := 
forall (b_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) + (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 >= 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) >= 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) + (Zabs (m)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
|--
  “ (same_sign (n + m ) retval ) ”
.

Definition mpz_add_return_wit_1_split_goal_spatial := 
forall (b_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) + (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 >= 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) >= 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) + (Zabs (m)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
|--
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs ((n + m ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
.

Definition mpz_add_return_wit_2 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) + (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 < 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) >= 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-retval))
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) + (Zabs (m)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
|--
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z r_pre (n + m ) )
) \/
(
forall (b_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) + (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 < 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) >= 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) + (Zabs (m)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
|--
  “ ((Zabs ((-retval))) <= cap_4) ” 
  &&  “ (same_sign (n + m ) (-retval) ) ”
  &&  (UIntArray.undef_seg ptr_2 (Zabs ((-retval))) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs ((n + m ))) (Zabs ((-retval))) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
).

Definition mpz_add_return_wit_2_split_goal_1 := 
forall (b_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) + (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 < 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) >= 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) + (Zabs (m)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
|--
  “ ((Zabs ((-retval))) <= cap_4) ”
.

Definition mpz_add_return_wit_2_split_goal_2 := 
forall (b_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) + (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 < 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) >= 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) + (Zabs (m)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
|--
  “ (same_sign (n + m ) (-retval) ) ”
.

Definition mpz_add_return_wit_2_split_goal_spatial := 
forall (b_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) + (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 < 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) >= 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) + (Zabs (m)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
|--
  (UIntArray.undef_seg ptr_2 (Zabs ((-retval))) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs ((n + m ))) (Zabs ((-retval))) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
.

Definition mpz_add_return_wit_3 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) - (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 >= 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) < 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> retval)
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) - (Zabs (m)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
|--
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z r_pre (n + m ) )
) \/
(
forall (b_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) - (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 >= 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) < 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) - (Zabs (m)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
|--
  “ (same_sign (n + m ) retval ) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs ((n + m ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
).

Definition mpz_add_return_wit_3_split_goal_1 := 
forall (b_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) - (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 >= 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) < 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) - (Zabs (m)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
|--
  “ (same_sign (n + m ) retval ) ”
.

Definition mpz_add_return_wit_3_split_goal_spatial := 
forall (b_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) - (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 >= 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) < 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) - (Zabs (m)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
|--
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs ((n + m ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
.

Definition mpz_add_return_wit_4 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) - (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 < 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) < 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-retval))
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) - (Zabs (m)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
|--
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z r_pre (n + m ) )
) \/
(
forall (b_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) - (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 < 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) < 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) - (Zabs (m)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
|--
  “ ((Zabs ((-retval))) <= cap_4) ” 
  &&  “ (same_sign (n + m ) (-retval) ) ”
  &&  (UIntArray.undef_seg ptr_2 (Zabs ((-retval))) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs ((n + m ))) (Zabs ((-retval))) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
).

Definition mpz_add_return_wit_4_split_goal_1 := 
forall (b_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) - (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 < 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) < 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) - (Zabs (m)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
|--
  “ ((Zabs ((-retval))) <= cap_4) ”
.

Definition mpz_add_return_wit_4_split_goal_2 := 
forall (b_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) - (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 < 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) < 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) - (Zabs (m)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
|--
  “ (same_sign (n + m ) (-retval) ) ”
.

Definition mpz_add_return_wit_4_split_goal_spatial := 
forall (b_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) - (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 < 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) < 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) - (Zabs (m)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
|--
  (UIntArray.undef_seg ptr_2 (Zabs ((-retval))) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs ((n + m ))) (Zabs ((-retval))) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
.

Definition mpz_add_partial_solve_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) ,
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
|--
  EX (cap: Z)  (size: Z)  (ptr: Z) ,
  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
.

Definition mpz_add_partial_solve_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign n size )) (PreH2 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
|--
  EX (cap_2: Z)  (size_2: Z)  (ptr_2: Z) ,
  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
.

Definition mpz_add_partial_solve_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : ((Z.lxor size size_2) >= 0)) (PreH2 : (same_sign m size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (same_sign n size )) (PreH5 : ((Zabs (size)) <= cap)) ,
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
|--
  “ ((Z.lxor size size_2) >= 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
.

Definition mpz_add_partial_solve_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : ((Z.lxor size size_2) < 0)) (PreH2 : (same_sign m size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (same_sign n size )) (PreH5 : ((Zabs (size)) <= cap)) ,
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
|--
  “ ((Z.lxor size size_2) < 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
.

Definition mpz_add_partial_solve_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (PreH1 : ((Z.lxor size size_2) >= 0)) (PreH2 : (same_sign m size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (same_sign n size )) (PreH5 : ((Zabs (size)) <= cap)) ,
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) + (Zabs (m)) ) retval )
|--
  EX (cap_3: Z)  (size_3: Z)  (ptr: Z) ,
  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) >= 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) + (Zabs (m)) ) retval )
.

Definition mpz_add_partial_solve_wit_6 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 >= 0)) (PreH2 : (same_sign n size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : ((Z.lxor size size_2) >= 0)) (PreH5 : (same_sign m size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign n size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) + (Zabs (m)) ) retval )
|--
  EX (cap_4: Z)  (ptr_2: Z) ,
  “ (same_sign ((Zabs (n)) + (Zabs (m)) ) retval ) ” 
  &&  “ ((Zabs (retval)) <= cap_4) ” 
  &&  “ (size_3 >= 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) >= 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) + (Zabs (m)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
.

Definition mpz_add_partial_solve_wit_7 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 < 0)) (PreH2 : (same_sign n size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : ((Z.lxor size size_2) >= 0)) (PreH5 : (same_sign m size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign n size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) + (Zabs (m)) ) retval )
|--
  EX (cap_4: Z)  (ptr_2: Z) ,
  “ (same_sign ((Zabs (n)) + (Zabs (m)) ) retval ) ” 
  &&  “ ((Zabs (retval)) <= cap_4) ” 
  &&  “ (size_3 < 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) >= 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) + (Zabs (m)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
.

Definition mpz_add_partial_solve_wit_8 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (PreH1 : ((Z.lxor size size_2) < 0)) (PreH2 : (same_sign m size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (same_sign n size )) (PreH5 : ((Zabs (size)) <= cap)) ,
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) retval )
|--
  EX (cap_3: Z)  (size_3: Z)  (ptr: Z) ,
  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) < 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) retval )
.

Definition mpz_add_partial_solve_wit_9 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 >= 0)) (PreH2 : (same_sign n size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : ((Z.lxor size size_2) < 0)) (PreH5 : (same_sign m size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign n size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) retval )
|--
  EX (cap_4: Z)  (ptr_2: Z) ,
  “ (same_sign ((Zabs (n)) - (Zabs (m)) ) retval ) ” 
  &&  “ ((Zabs (retval)) <= cap_4) ” 
  &&  “ (size_3 >= 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) < 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) - (Zabs (m)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
.

Definition mpz_add_partial_solve_wit_10 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 < 0)) (PreH2 : (same_sign n size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : ((Z.lxor size size_2) < 0)) (PreH5 : (same_sign m size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign n size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) retval )
|--
  EX (cap_4: Z)  (ptr_2: Z) ,
  “ (same_sign ((Zabs (n)) - (Zabs (m)) ) retval ) ” 
  &&  “ ((Zabs (retval)) <= cap_4) ” 
  &&  “ (size_3 < 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) < 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) - (Zabs (m)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
.

(*----- Function mpz_sub -----*)

Definition mpz_sub_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign m size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (same_sign n size )) (PreH4 : ((Zabs (size)) <= cap)) ,
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_Z r_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_sub_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign n size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : ((Z.lxor size size_2) >= 0)) (PreH4 : (same_sign m size_2 )) (PreH5 : ((Zabs (size_2)) <= cap_2)) (PreH6 : (same_sign n size )) (PreH7 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) retval )
  **  ((( &( "rn" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_sub_safety_wit_3 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 < 0)) (PreH2 : (same_sign n size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : ((Z.lxor size size_2) >= 0)) (PreH5 : (same_sign m size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign n size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) retval )
  **  ((( &( "rn" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (retval <> (INT_MIN)) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 < 0)) (PreH2 : (same_sign n size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : ((Z.lxor size size_2) >= 0)) (PreH5 : (same_sign m size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign n size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) retval )
  **  ((( &( "rn" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (retval <> (INT_MIN)) ”
).

Definition mpz_sub_safety_wit_3_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 < 0)) (PreH2 : (same_sign n size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : ((Z.lxor size size_2) >= 0)) (PreH5 : (same_sign m size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign n size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) retval )
  **  ((( &( "rn" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (retval <> (INT_MIN)) ”
.

Definition mpz_sub_safety_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (same_sign n size_3 )) (PreH2 : ((Zabs (size_3)) <= cap_3)) (PreH3 : ((Z.lxor size size_2) < 0)) (PreH4 : (same_sign m size_2 )) (PreH5 : ((Zabs (size_2)) <= cap_2)) (PreH6 : (same_sign n size )) (PreH7 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) + (Zabs (m)) ) retval )
  **  ((( &( "rn" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_sub_safety_wit_5 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 < 0)) (PreH2 : (same_sign n size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : ((Z.lxor size size_2) < 0)) (PreH5 : (same_sign m size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign n size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) + (Zabs (m)) ) retval )
  **  ((( &( "rn" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (retval <> (INT_MIN)) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 < 0)) (PreH2 : (same_sign n size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : ((Z.lxor size size_2) < 0)) (PreH5 : (same_sign m size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign n size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) + (Zabs (m)) ) retval )
  **  ((( &( "rn" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (retval <> (INT_MIN)) ”
).

Definition mpz_sub_safety_wit_5_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 < 0)) (PreH2 : (same_sign n size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : ((Z.lxor size size_2) < 0)) (PreH5 : (same_sign m size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign n size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) + (Zabs (m)) ) retval )
  **  ((( &( "rn" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (retval <> (INT_MIN)) ”
.

Definition mpz_sub_return_wit_1 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) - (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 >= 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) >= 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> retval)
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) - (Zabs (m)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
|--
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z r_pre (n - m ) )
) \/
(
forall (b_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) - (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 >= 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) >= 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) - (Zabs (m)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
|--
  “ (same_sign (n - m ) retval ) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs ((n - m ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
).

Definition mpz_sub_return_wit_1_split_goal_1 := 
forall (b_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) - (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 >= 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) >= 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) - (Zabs (m)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
|--
  “ (same_sign (n - m ) retval ) ”
.

Definition mpz_sub_return_wit_1_split_goal_spatial := 
forall (b_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) - (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 >= 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) >= 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) - (Zabs (m)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
|--
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs ((n - m ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
.

Definition mpz_sub_return_wit_2 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) - (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 < 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) >= 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-retval))
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) - (Zabs (m)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
|--
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z r_pre (n - m ) )
) \/
(
forall (b_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) - (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 < 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) >= 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) - (Zabs (m)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
|--
  “ ((Zabs ((-retval))) <= cap_4) ” 
  &&  “ (same_sign (n - m ) (-retval) ) ”
  &&  (UIntArray.undef_seg ptr_2 (Zabs ((-retval))) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs ((n - m ))) (Zabs ((-retval))) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
).

Definition mpz_sub_return_wit_2_split_goal_1 := 
forall (b_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) - (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 < 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) >= 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) - (Zabs (m)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
|--
  “ ((Zabs ((-retval))) <= cap_4) ”
.

Definition mpz_sub_return_wit_2_split_goal_2 := 
forall (b_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) - (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 < 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) >= 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) - (Zabs (m)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
|--
  “ (same_sign (n - m ) (-retval) ) ”
.

Definition mpz_sub_return_wit_2_split_goal_spatial := 
forall (b_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) - (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 < 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) >= 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) - (Zabs (m)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
|--
  (UIntArray.undef_seg ptr_2 (Zabs ((-retval))) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs ((n - m ))) (Zabs ((-retval))) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
.

Definition mpz_sub_return_wit_3 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) + (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 >= 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) < 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> retval)
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) + (Zabs (m)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
|--
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z r_pre (n - m ) )
) \/
(
forall (b_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) + (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 >= 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) < 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) + (Zabs (m)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
|--
  “ (same_sign (n - m ) retval ) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs ((n - m ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
).

Definition mpz_sub_return_wit_3_split_goal_1 := 
forall (b_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) + (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 >= 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) < 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) + (Zabs (m)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
|--
  “ (same_sign (n - m ) retval ) ”
.

Definition mpz_sub_return_wit_3_split_goal_spatial := 
forall (b_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) + (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 >= 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) < 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) + (Zabs (m)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
|--
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs ((n - m ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
.

Definition mpz_sub_return_wit_4 := 
(
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) + (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 < 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) < 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-retval))
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) + (Zabs (m)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
|--
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z r_pre (n - m ) )
) \/
(
forall (b_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) + (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 < 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) < 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) + (Zabs (m)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
|--
  “ ((Zabs ((-retval))) <= cap_4) ” 
  &&  “ (same_sign (n - m ) (-retval) ) ”
  &&  (UIntArray.undef_seg ptr_2 (Zabs ((-retval))) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs ((n - m ))) (Zabs ((-retval))) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
).

Definition mpz_sub_return_wit_4_split_goal_1 := 
forall (b_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) + (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 < 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) < 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) + (Zabs (m)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
|--
  “ ((Zabs ((-retval))) <= cap_4) ”
.

Definition mpz_sub_return_wit_4_split_goal_2 := 
forall (b_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) + (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 < 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) < 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) + (Zabs (m)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
|--
  “ (same_sign (n - m ) (-retval) ) ”
.

Definition mpz_sub_return_wit_4_split_goal_spatial := 
forall (b_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (ptr_2: Z) (cap_4: Z) (PreH1 : (same_sign ((Zabs (n)) + (Zabs (m)) ) retval )) (PreH2 : ((Zabs (retval)) <= cap_4)) (PreH3 : (size_3 < 0)) (PreH4 : (same_sign n size_3 )) (PreH5 : ((Zabs (size_3)) <= cap_3)) (PreH6 : ((Z.lxor size size_2) < 0)) (PreH7 : (same_sign m size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (same_sign n size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) + (Zabs (m)) ))) (Zabs (retval)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
|--
  (UIntArray.undef_seg ptr_2 (Zabs ((-retval))) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs ((n - m ))) (Zabs ((-retval))) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  (store_Z b_pre m )
.

Definition mpz_sub_partial_solve_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) ,
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
|--
  EX (cap: Z)  (size: Z)  (ptr: Z) ,
  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
.

Definition mpz_sub_partial_solve_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign n size )) (PreH2 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
|--
  EX (cap_2: Z)  (size_2: Z)  (ptr_2: Z) ,
  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
.

Definition mpz_sub_partial_solve_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : ((Z.lxor size size_2) >= 0)) (PreH2 : (same_sign m size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (same_sign n size )) (PreH5 : ((Zabs (size)) <= cap)) ,
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
|--
  “ ((Z.lxor size size_2) >= 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
.

Definition mpz_sub_partial_solve_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (l: Z) (m: Z) (n: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : ((Z.lxor size size_2) < 0)) (PreH2 : (same_sign m size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (same_sign n size )) (PreH5 : ((Zabs (size)) <= cap)) ,
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (m)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z r_pre l )
|--
  “ ((Z.lxor size size_2) < 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z r_pre l )
.

Definition mpz_sub_partial_solve_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (PreH1 : ((Z.lxor size size_2) >= 0)) (PreH2 : (same_sign m size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (same_sign n size )) (PreH5 : ((Zabs (size)) <= cap)) ,
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) retval )
|--
  EX (cap_3: Z)  (size_3: Z)  (ptr: Z) ,
  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) >= 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) retval )
.

Definition mpz_sub_partial_solve_wit_6 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 >= 0)) (PreH2 : (same_sign n size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : ((Z.lxor size size_2) >= 0)) (PreH5 : (same_sign m size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign n size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) retval )
|--
  EX (cap_4: Z)  (ptr_2: Z) ,
  “ (same_sign ((Zabs (n)) - (Zabs (m)) ) retval ) ” 
  &&  “ ((Zabs (retval)) <= cap_4) ” 
  &&  “ (size_3 >= 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) >= 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) - (Zabs (m)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
.

Definition mpz_sub_partial_solve_wit_7 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 < 0)) (PreH2 : (same_sign n size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : ((Z.lxor size size_2) >= 0)) (PreH5 : (same_sign m size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign n size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) - (Zabs (m)) ) retval )
|--
  EX (cap_4: Z)  (ptr_2: Z) ,
  “ (same_sign ((Zabs (n)) - (Zabs (m)) ) retval ) ” 
  &&  “ ((Zabs (retval)) <= cap_4) ” 
  &&  “ (size_3 < 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) >= 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) - (Zabs (m)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
.

Definition mpz_sub_partial_solve_wit_8 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (PreH1 : ((Z.lxor size size_2) < 0)) (PreH2 : (same_sign m size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (same_sign n size )) (PreH5 : ((Zabs (size)) <= cap)) ,
  (store_Z a_pre n )
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) + (Zabs (m)) ) retval )
|--
  EX (cap_3: Z)  (size_3: Z)  (ptr: Z) ,
  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) < 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) + (Zabs (m)) ) retval )
.

Definition mpz_sub_partial_solve_wit_9 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 >= 0)) (PreH2 : (same_sign n size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : ((Z.lxor size size_2) < 0)) (PreH5 : (same_sign m size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign n size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) + (Zabs (m)) ) retval )
|--
  EX (cap_4: Z)  (ptr_2: Z) ,
  “ (same_sign ((Zabs (n)) + (Zabs (m)) ) retval ) ” 
  &&  “ ((Zabs (retval)) <= cap_4) ” 
  &&  “ (size_3 >= 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) < 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) + (Zabs (m)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
.

Definition mpz_sub_partial_solve_wit_10 := 
forall (b_pre: Z) (a_pre: Z) (r_pre: Z) (m: Z) (n: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (retval: Z) (ptr: Z) (size_3: Z) (cap_3: Z) (PreH1 : (size_3 < 0)) (PreH2 : (same_sign n size_3 )) (PreH3 : ((Zabs (size_3)) <= cap_3)) (PreH4 : ((Z.lxor size size_2) < 0)) (PreH5 : (same_sign m size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (same_sign n size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
  **  (store_Z_remain_size r_pre ((Zabs (n)) + (Zabs (m)) ) retval )
|--
  EX (cap_4: Z)  (ptr_2: Z) ,
  “ (same_sign ((Zabs (n)) + (Zabs (m)) ) retval ) ” 
  &&  “ ((Zabs (retval)) <= cap_4) ” 
  &&  “ (size_3 < 0) ” 
  &&  “ (same_sign n size_3 ) ” 
  &&  “ ((Zabs (size_3)) <= cap_3) ” 
  &&  “ ((Z.lxor size size_2) < 0) ” 
  &&  “ (same_sign m size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign n size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.undef_seg ptr_2 (Zabs (retval)) cap_4 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (((Zabs (n)) + (Zabs (m)) ))) (Zabs (retval)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_4)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_3)
  **  (UIntArray.undef_seg ptr (Zabs (size_3)) cap_3 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (n)) (Zabs (size_3)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_3)
  **  (store_Z b_pre m )
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.

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
Axiom proof_of_mpn_copyi_safety_wit_1 : mpn_copyi_safety_wit_1.
Axiom proof_of_mpn_copyi_safety_wit_2 : mpn_copyi_safety_wit_2.
Axiom proof_of_mpn_copyi_entail_wit_1 : mpn_copyi_entail_wit_1.
Axiom proof_of_mpn_copyi_entail_wit_2 : mpn_copyi_entail_wit_2.
Axiom proof_of_mpn_copyi_return_wit_1 : mpn_copyi_return_wit_1.
Axiom proof_of_mpn_copyi_partial_solve_wit_1 : mpn_copyi_partial_solve_wit_1.
Axiom proof_of_mpn_copyi_partial_solve_wit_2 : mpn_copyi_partial_solve_wit_2.
Axiom proof_of_mpn_copyi_partial_solve_wit_3 : mpn_copyi_partial_solve_wit_3.
Axiom proof_of_mpn_copyi_which_implies_wit_1 : mpn_copyi_which_implies_wit_1.
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
Axiom proof_of_mpn_normalized_size_safety_wit_1 : mpn_normalized_size_safety_wit_1.
Axiom proof_of_mpn_normalized_size_safety_wit_2 : mpn_normalized_size_safety_wit_2.
Axiom proof_of_mpn_normalized_size_safety_wit_3 : mpn_normalized_size_safety_wit_3.
Axiom proof_of_mpn_normalized_size_safety_wit_4 : mpn_normalized_size_safety_wit_4.
Axiom proof_of_mpn_normalized_size_safety_wit_5 : mpn_normalized_size_safety_wit_5.
Axiom proof_of_mpn_normalized_size_entail_wit_1 : mpn_normalized_size_entail_wit_1.
Axiom proof_of_mpn_normalized_size_entail_wit_2 : mpn_normalized_size_entail_wit_2.
Axiom proof_of_mpn_normalized_size_entail_wit_3 : mpn_normalized_size_entail_wit_3.
Axiom proof_of_mpn_normalized_size_return_wit_1 : mpn_normalized_size_return_wit_1.
Axiom proof_of_mpn_normalized_size_return_wit_2 : mpn_normalized_size_return_wit_2.
Axiom proof_of_mpn_normalized_size_partial_solve_wit_1 : mpn_normalized_size_partial_solve_wit_1.
Axiom proof_of_mpn_normalized_size_partial_solve_wit_2 : mpn_normalized_size_partial_solve_wit_2.
Axiom proof_of_mpn_normalized_size_which_implies_wit_1 : mpn_normalized_size_which_implies_wit_1.
Axiom proof_of_mpn_add_1_safety_wit_1 : mpn_add_1_safety_wit_1.
Axiom proof_of_mpn_add_1_safety_wit_2 : mpn_add_1_safety_wit_2.
Axiom proof_of_mpn_add_1_safety_wit_3 : mpn_add_1_safety_wit_3.
Axiom proof_of_mpn_add_1_safety_wit_4 : mpn_add_1_safety_wit_4.
Axiom proof_of_mpn_add_1_safety_wit_5 : mpn_add_1_safety_wit_5.
Axiom proof_of_mpn_add_1_entail_wit_1_1 : mpn_add_1_entail_wit_1_1.
Axiom proof_of_mpn_add_1_entail_wit_1_2 : mpn_add_1_entail_wit_1_2.
Axiom proof_of_mpn_add_1_entail_wit_2_1 : mpn_add_1_entail_wit_2_1.
Axiom proof_of_mpn_add_1_entail_wit_2_2 : mpn_add_1_entail_wit_2_2.
Axiom proof_of_mpn_add_1_return_wit_1 : mpn_add_1_return_wit_1.
Axiom proof_of_mpn_add_1_partial_solve_wit_1 : mpn_add_1_partial_solve_wit_1.
Axiom proof_of_mpn_add_1_partial_solve_wit_2 : mpn_add_1_partial_solve_wit_2.
Axiom proof_of_mpn_add_1_partial_solve_wit_3 : mpn_add_1_partial_solve_wit_3.
Axiom proof_of_mpn_add_1_partial_solve_wit_4 : mpn_add_1_partial_solve_wit_4.
Axiom proof_of_mpn_add_1_partial_solve_wit_5 : mpn_add_1_partial_solve_wit_5.
Axiom proof_of_mpn_add_1_partial_solve_wit_6 : mpn_add_1_partial_solve_wit_6.
Axiom proof_of_mpn_add_1_partial_solve_wit_7 : mpn_add_1_partial_solve_wit_7.
Axiom proof_of_mpn_add_1_which_implies_wit_1 : mpn_add_1_which_implies_wit_1.
Axiom proof_of_mpn_add_n_safety_wit_1 : mpn_add_n_safety_wit_1.
Axiom proof_of_mpn_add_n_safety_wit_2 : mpn_add_n_safety_wit_2.
Axiom proof_of_mpn_add_n_safety_wit_3 : mpn_add_n_safety_wit_3.
Axiom proof_of_mpn_add_n_safety_wit_4 : mpn_add_n_safety_wit_4.
Axiom proof_of_mpn_add_n_safety_wit_5 : mpn_add_n_safety_wit_5.
Axiom proof_of_mpn_add_n_safety_wit_6 : mpn_add_n_safety_wit_6.
Axiom proof_of_mpn_add_n_entail_wit_1 : mpn_add_n_entail_wit_1.
Axiom proof_of_mpn_add_n_entail_wit_2_1 : mpn_add_n_entail_wit_2_1.
Axiom proof_of_mpn_add_n_entail_wit_2_2 : mpn_add_n_entail_wit_2_2.
Axiom proof_of_mpn_add_n_entail_wit_2_3 : mpn_add_n_entail_wit_2_3.
Axiom proof_of_mpn_add_n_entail_wit_2_4 : mpn_add_n_entail_wit_2_4.
Axiom proof_of_mpn_add_n_return_wit_1 : mpn_add_n_return_wit_1.
Axiom proof_of_mpn_add_n_partial_solve_wit_1 : mpn_add_n_partial_solve_wit_1.
Axiom proof_of_mpn_add_n_partial_solve_wit_2 : mpn_add_n_partial_solve_wit_2.
Axiom proof_of_mpn_add_n_partial_solve_wit_3 : mpn_add_n_partial_solve_wit_3.
Axiom proof_of_mpn_add_n_partial_solve_wit_4 : mpn_add_n_partial_solve_wit_4.
Axiom proof_of_mpn_add_n_partial_solve_wit_5 : mpn_add_n_partial_solve_wit_5.
Axiom proof_of_mpn_add_n_partial_solve_wit_6 : mpn_add_n_partial_solve_wit_6.
Axiom proof_of_mpn_add_n_partial_solve_wit_7 : mpn_add_n_partial_solve_wit_7.
Axiom proof_of_mpn_add_n_which_implies_wit_1 : mpn_add_n_which_implies_wit_1.
Axiom proof_of_mpn_add_safety_wit_1 : mpn_add_safety_wit_1.
Axiom proof_of_mpn_add_entail_wit_1 : mpn_add_entail_wit_1.
Axiom proof_of_mpn_add_return_wit_1 : mpn_add_return_wit_1.
Axiom proof_of_mpn_add_return_wit_2 : mpn_add_return_wit_2.
Axiom proof_of_mpn_add_partial_solve_wit_1_pure : mpn_add_partial_solve_wit_1_pure.
Axiom proof_of_mpn_add_partial_solve_wit_1 : mpn_add_partial_solve_wit_1.
Axiom proof_of_mpn_add_partial_solve_wit_2_pure : mpn_add_partial_solve_wit_2_pure.
Axiom proof_of_mpn_add_partial_solve_wit_2 : mpn_add_partial_solve_wit_2.
Axiom proof_of_mpn_add_partial_solve_wit_3_pure : mpn_add_partial_solve_wit_3_pure.
Axiom proof_of_mpn_add_partial_solve_wit_3 : mpn_add_partial_solve_wit_3.
Axiom proof_of_mpn_add_partial_solve_wit_4 : mpn_add_partial_solve_wit_4.
Axiom proof_of_mpn_add_partial_solve_wit_5_pure : mpn_add_partial_solve_wit_5_pure.
Axiom proof_of_mpn_add_partial_solve_wit_5 : mpn_add_partial_solve_wit_5.
Axiom proof_of_mpn_add_which_implies_wit_1 : mpn_add_which_implies_wit_1.
Axiom proof_of_mpn_add_which_implies_wit_2 : mpn_add_which_implies_wit_2.
Axiom proof_of_mpn_add_which_implies_wit_3 : mpn_add_which_implies_wit_3.
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
Axiom proof_of_mpn_sub_1_safety_wit_1 : mpn_sub_1_safety_wit_1.
Axiom proof_of_mpn_sub_1_safety_wit_2 : mpn_sub_1_safety_wit_2.
Axiom proof_of_mpn_sub_1_safety_wit_3 : mpn_sub_1_safety_wit_3.
Axiom proof_of_mpn_sub_1_safety_wit_4 : mpn_sub_1_safety_wit_4.
Axiom proof_of_mpn_sub_1_safety_wit_5 : mpn_sub_1_safety_wit_5.
Axiom proof_of_mpn_sub_1_entail_wit_1_1 : mpn_sub_1_entail_wit_1_1.
Axiom proof_of_mpn_sub_1_entail_wit_1_2 : mpn_sub_1_entail_wit_1_2.
Axiom proof_of_mpn_sub_1_entail_wit_2_1 : mpn_sub_1_entail_wit_2_1.
Axiom proof_of_mpn_sub_1_entail_wit_2_2 : mpn_sub_1_entail_wit_2_2.
Axiom proof_of_mpn_sub_1_return_wit_1 : mpn_sub_1_return_wit_1.
Axiom proof_of_mpn_sub_1_partial_solve_wit_1 : mpn_sub_1_partial_solve_wit_1.
Axiom proof_of_mpn_sub_1_partial_solve_wit_2 : mpn_sub_1_partial_solve_wit_2.
Axiom proof_of_mpn_sub_1_partial_solve_wit_3 : mpn_sub_1_partial_solve_wit_3.
Axiom proof_of_mpn_sub_1_partial_solve_wit_4 : mpn_sub_1_partial_solve_wit_4.
Axiom proof_of_mpn_sub_1_partial_solve_wit_5 : mpn_sub_1_partial_solve_wit_5.
Axiom proof_of_mpn_sub_1_partial_solve_wit_6 : mpn_sub_1_partial_solve_wit_6.
Axiom proof_of_mpn_sub_1_partial_solve_wit_7 : mpn_sub_1_partial_solve_wit_7.
Axiom proof_of_mpn_sub_1_which_implies_wit_1 : mpn_sub_1_which_implies_wit_1.
Axiom proof_of_mpn_sub_n_safety_wit_1 : mpn_sub_n_safety_wit_1.
Axiom proof_of_mpn_sub_n_safety_wit_2 : mpn_sub_n_safety_wit_2.
Axiom proof_of_mpn_sub_n_safety_wit_3 : mpn_sub_n_safety_wit_3.
Axiom proof_of_mpn_sub_n_safety_wit_4 : mpn_sub_n_safety_wit_4.
Axiom proof_of_mpn_sub_n_safety_wit_5 : mpn_sub_n_safety_wit_5.
Axiom proof_of_mpn_sub_n_safety_wit_6 : mpn_sub_n_safety_wit_6.
Axiom proof_of_mpn_sub_n_entail_wit_1 : mpn_sub_n_entail_wit_1.
Axiom proof_of_mpn_sub_n_entail_wit_2_1 : mpn_sub_n_entail_wit_2_1.
Axiom proof_of_mpn_sub_n_entail_wit_2_2 : mpn_sub_n_entail_wit_2_2.
Axiom proof_of_mpn_sub_n_entail_wit_2_3 : mpn_sub_n_entail_wit_2_3.
Axiom proof_of_mpn_sub_n_entail_wit_2_4 : mpn_sub_n_entail_wit_2_4.
Axiom proof_of_mpn_sub_n_return_wit_1 : mpn_sub_n_return_wit_1.
Axiom proof_of_mpn_sub_n_partial_solve_wit_1 : mpn_sub_n_partial_solve_wit_1.
Axiom proof_of_mpn_sub_n_partial_solve_wit_2 : mpn_sub_n_partial_solve_wit_2.
Axiom proof_of_mpn_sub_n_partial_solve_wit_3 : mpn_sub_n_partial_solve_wit_3.
Axiom proof_of_mpn_sub_n_partial_solve_wit_4 : mpn_sub_n_partial_solve_wit_4.
Axiom proof_of_mpn_sub_n_partial_solve_wit_5 : mpn_sub_n_partial_solve_wit_5.
Axiom proof_of_mpn_sub_n_partial_solve_wit_6 : mpn_sub_n_partial_solve_wit_6.
Axiom proof_of_mpn_sub_n_partial_solve_wit_7 : mpn_sub_n_partial_solve_wit_7.
Axiom proof_of_mpn_sub_n_which_implies_wit_1 : mpn_sub_n_which_implies_wit_1.
Axiom proof_of_mpn_sub_safety_wit_1 : mpn_sub_safety_wit_1.
Axiom proof_of_mpn_sub_entail_wit_1 : mpn_sub_entail_wit_1.
Axiom proof_of_mpn_sub_entail_wit_2 : mpn_sub_entail_wit_2.
Axiom proof_of_mpn_sub_return_wit_1 : mpn_sub_return_wit_1.
Axiom proof_of_mpn_sub_return_wit_2 : mpn_sub_return_wit_2.
Axiom proof_of_mpn_sub_partial_solve_wit_1_pure : mpn_sub_partial_solve_wit_1_pure.
Axiom proof_of_mpn_sub_partial_solve_wit_1 : mpn_sub_partial_solve_wit_1.
Axiom proof_of_mpn_sub_partial_solve_wit_2_pure : mpn_sub_partial_solve_wit_2_pure.
Axiom proof_of_mpn_sub_partial_solve_wit_2 : mpn_sub_partial_solve_wit_2.
Axiom proof_of_mpn_sub_partial_solve_wit_3_pure : mpn_sub_partial_solve_wit_3_pure.
Axiom proof_of_mpn_sub_partial_solve_wit_3 : mpn_sub_partial_solve_wit_3.
Axiom proof_of_mpn_sub_partial_solve_wit_4 : mpn_sub_partial_solve_wit_4.
Axiom proof_of_mpn_sub_partial_solve_wit_5_pure : mpn_sub_partial_solve_wit_5_pure.
Axiom proof_of_mpn_sub_partial_solve_wit_5 : mpn_sub_partial_solve_wit_5.
Axiom proof_of_mpn_sub_which_implies_wit_1 : mpn_sub_which_implies_wit_1.
Axiom proof_of_mpn_sub_which_implies_wit_2 : mpn_sub_which_implies_wit_2.
Axiom proof_of_mpn_sub_which_implies_wit_3 : mpn_sub_which_implies_wit_3.
Axiom proof_of_mpz_clear_return_wit_1 : mpz_clear_return_wit_1.
Axiom proof_of_mpz_clear_return_wit_2 : mpz_clear_return_wit_2.
Axiom proof_of_mpz_clear_partial_solve_wit_1 : mpz_clear_partial_solve_wit_1.
Axiom proof_of_mpz_clear_partial_solve_wit_2 : mpz_clear_partial_solve_wit_2.
Axiom proof_of_mpz_realloc_safety_wit_1 : mpz_realloc_safety_wit_1.
Axiom proof_of_mpz_realloc_safety_wit_2 : mpz_realloc_safety_wit_2.
Axiom proof_of_mpz_realloc_safety_wit_3 : mpz_realloc_safety_wit_3.
Axiom proof_of_mpz_realloc_return_wit_1 : mpz_realloc_return_wit_1.
Axiom proof_of_mpz_realloc_return_wit_2 : mpz_realloc_return_wit_2.
Axiom proof_of_mpz_realloc_return_wit_3 : mpz_realloc_return_wit_3.
Axiom proof_of_mpz_realloc_return_wit_4 : mpz_realloc_return_wit_4.
Axiom proof_of_mpz_realloc_partial_solve_wit_1 : mpz_realloc_partial_solve_wit_1.
Axiom proof_of_mpz_realloc_partial_solve_wit_2_pure : mpz_realloc_partial_solve_wit_2_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_2 : mpz_realloc_partial_solve_wit_2.
Axiom proof_of_mpz_realloc_partial_solve_wit_3_pure : mpz_realloc_partial_solve_wit_3_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_3 : mpz_realloc_partial_solve_wit_3.
Axiom proof_of_mpz_realloc_partial_solve_wit_4_pure : mpz_realloc_partial_solve_wit_4_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_4 : mpz_realloc_partial_solve_wit_4.
Axiom proof_of_mpz_realloc_partial_solve_wit_5_pure : mpz_realloc_partial_solve_wit_5_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_5 : mpz_realloc_partial_solve_wit_5.
Axiom proof_of_mrz_realloc_if_return_wit_1 : mrz_realloc_if_return_wit_1.
Axiom proof_of_mrz_realloc_if_return_wit_2 : mrz_realloc_if_return_wit_2.
Axiom proof_of_mrz_realloc_if_partial_solve_wit_1_pure : mrz_realloc_if_partial_solve_wit_1_pure.
Axiom proof_of_mrz_realloc_if_partial_solve_wit_1 : mrz_realloc_if_partial_solve_wit_1.
Axiom proof_of_mpz_sgn_safety_wit_1 : mpz_sgn_safety_wit_1.
Axiom proof_of_mpz_sgn_return_wit_1 : mpz_sgn_return_wit_1.
Axiom proof_of_mpz_sgn_return_wit_2 : mpz_sgn_return_wit_2.
Axiom proof_of_mpz_sgn_return_wit_3 : mpz_sgn_return_wit_3.
Axiom proof_of_mpz_sgn_partial_solve_wit_1 : mpz_sgn_partial_solve_wit_1.
Axiom proof_of_mpz_sgn_partial_solve_wit_2 : mpz_sgn_partial_solve_wit_2.
Axiom proof_of_mpz_swap_return_wit_1 : mpz_swap_return_wit_1.
Axiom proof_of_mpz_swap_partial_solve_wit_1 : mpz_swap_partial_solve_wit_1.
Axiom proof_of_mpz_swap_partial_solve_wit_2 : mpz_swap_partial_solve_wit_2.
Axiom proof_of_mpz_swap_partial_solve_wit_3 : mpz_swap_partial_solve_wit_3.
Axiom proof_of_mpz_abs_add_safety_wit_1 : mpz_abs_add_safety_wit_1.
Axiom proof_of_mpz_abs_add_safety_wit_2 : mpz_abs_add_safety_wit_2.
Axiom proof_of_mpz_abs_add_entail_wit_1_1 : mpz_abs_add_entail_wit_1_1.
Axiom proof_of_mpz_abs_add_entail_wit_1_2 : mpz_abs_add_entail_wit_1_2.
Axiom proof_of_mpz_abs_add_entail_wit_2 : mpz_abs_add_entail_wit_2.
Axiom proof_of_mpz_abs_add_return_wit_1 : mpz_abs_add_return_wit_1.
Axiom proof_of_mpz_abs_add_partial_solve_wit_1 : mpz_abs_add_partial_solve_wit_1.
Axiom proof_of_mpz_abs_add_partial_solve_wit_2_pure : mpz_abs_add_partial_solve_wit_2_pure.
Axiom proof_of_mpz_abs_add_partial_solve_wit_2 : mpz_abs_add_partial_solve_wit_2.
Axiom proof_of_mpz_abs_add_partial_solve_wit_3 : mpz_abs_add_partial_solve_wit_3.
Axiom proof_of_mpz_abs_add_partial_solve_wit_4_pure : mpz_abs_add_partial_solve_wit_4_pure.
Axiom proof_of_mpz_abs_add_partial_solve_wit_4 : mpz_abs_add_partial_solve_wit_4.
Axiom proof_of_mpz_abs_add_partial_solve_wit_5 : mpz_abs_add_partial_solve_wit_5.
Axiom proof_of_mpz_abs_add_partial_solve_wit_6 : mpz_abs_add_partial_solve_wit_6.
Axiom proof_of_mpz_abs_add_partial_solve_wit_7_pure : mpz_abs_add_partial_solve_wit_7_pure.
Axiom proof_of_mpz_abs_add_partial_solve_wit_7 : mpz_abs_add_partial_solve_wit_7.
Axiom proof_of_mpz_abs_add_partial_solve_wit_8_pure : mpz_abs_add_partial_solve_wit_8_pure.
Axiom proof_of_mpz_abs_add_partial_solve_wit_8 : mpz_abs_add_partial_solve_wit_8.
Axiom proof_of_mpz_abs_add_partial_solve_wit_9 : mpz_abs_add_partial_solve_wit_9.
Axiom proof_of_mpz_abs_sub_safety_wit_1 : mpz_abs_sub_safety_wit_1.
Axiom proof_of_mpz_abs_sub_safety_wit_2 : mpz_abs_sub_safety_wit_2.
Axiom proof_of_mpz_abs_sub_safety_wit_3 : mpz_abs_sub_safety_wit_3.
Axiom proof_of_mpz_abs_sub_safety_wit_4 : mpz_abs_sub_safety_wit_4.
Axiom proof_of_mpz_abs_sub_safety_wit_5 : mpz_abs_sub_safety_wit_5.
Axiom proof_of_mpz_abs_sub_safety_wit_6 : mpz_abs_sub_safety_wit_6.
Axiom proof_of_mpz_abs_sub_safety_wit_7 : mpz_abs_sub_safety_wit_7.
Axiom proof_of_mpz_abs_sub_safety_wit_8 : mpz_abs_sub_safety_wit_8.
Axiom proof_of_mpz_abs_sub_safety_wit_9 : mpz_abs_sub_safety_wit_9.
Axiom proof_of_mpz_abs_sub_safety_wit_10 : mpz_abs_sub_safety_wit_10.
Axiom proof_of_mpz_abs_sub_safety_wit_11 : mpz_abs_sub_safety_wit_11.
Axiom proof_of_mpz_abs_sub_safety_wit_12 : mpz_abs_sub_safety_wit_12.
Axiom proof_of_mpz_abs_sub_entail_wit_1 : mpz_abs_sub_entail_wit_1.
Axiom proof_of_mpz_abs_sub_entail_wit_2 : mpz_abs_sub_entail_wit_2.
Axiom proof_of_mpz_abs_sub_entail_wit_3 : mpz_abs_sub_entail_wit_3.
Axiom proof_of_mpz_abs_sub_entail_wit_4 : mpz_abs_sub_entail_wit_4.
Axiom proof_of_mpz_abs_sub_return_wit_1 : mpz_abs_sub_return_wit_1.
Axiom proof_of_mpz_abs_sub_return_wit_2 : mpz_abs_sub_return_wit_2.
Axiom proof_of_mpz_abs_sub_return_wit_3 : mpz_abs_sub_return_wit_3.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_1 : mpz_abs_sub_partial_solve_wit_1.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_2_pure : mpz_abs_sub_partial_solve_wit_2_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_2 : mpz_abs_sub_partial_solve_wit_2.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_3 : mpz_abs_sub_partial_solve_wit_3.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_4_pure : mpz_abs_sub_partial_solve_wit_4_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_4 : mpz_abs_sub_partial_solve_wit_4.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_5_pure : mpz_abs_sub_partial_solve_wit_5_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_5 : mpz_abs_sub_partial_solve_wit_5.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_6_pure : mpz_abs_sub_partial_solve_wit_6_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_6 : mpz_abs_sub_partial_solve_wit_6.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_7_pure : mpz_abs_sub_partial_solve_wit_7_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_7 : mpz_abs_sub_partial_solve_wit_7.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_8_pure : mpz_abs_sub_partial_solve_wit_8_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_8 : mpz_abs_sub_partial_solve_wit_8.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_9_pure : mpz_abs_sub_partial_solve_wit_9_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_9 : mpz_abs_sub_partial_solve_wit_9.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_10_pure : mpz_abs_sub_partial_solve_wit_10_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_10 : mpz_abs_sub_partial_solve_wit_10.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_11_pure : mpz_abs_sub_partial_solve_wit_11_pure.
Axiom proof_of_mpz_abs_sub_partial_solve_wit_11 : mpz_abs_sub_partial_solve_wit_11.
Axiom proof_of_mpz_add_safety_wit_1 : mpz_add_safety_wit_1.
Axiom proof_of_mpz_add_safety_wit_2 : mpz_add_safety_wit_2.
Axiom proof_of_mpz_add_safety_wit_3 : mpz_add_safety_wit_3.
Axiom proof_of_mpz_add_safety_wit_4 : mpz_add_safety_wit_4.
Axiom proof_of_mpz_add_safety_wit_5 : mpz_add_safety_wit_5.
Axiom proof_of_mpz_add_return_wit_1 : mpz_add_return_wit_1.
Axiom proof_of_mpz_add_return_wit_2 : mpz_add_return_wit_2.
Axiom proof_of_mpz_add_return_wit_3 : mpz_add_return_wit_3.
Axiom proof_of_mpz_add_return_wit_4 : mpz_add_return_wit_4.
Axiom proof_of_mpz_add_partial_solve_wit_1 : mpz_add_partial_solve_wit_1.
Axiom proof_of_mpz_add_partial_solve_wit_2 : mpz_add_partial_solve_wit_2.
Axiom proof_of_mpz_add_partial_solve_wit_3 : mpz_add_partial_solve_wit_3.
Axiom proof_of_mpz_add_partial_solve_wit_4 : mpz_add_partial_solve_wit_4.
Axiom proof_of_mpz_add_partial_solve_wit_5 : mpz_add_partial_solve_wit_5.
Axiom proof_of_mpz_add_partial_solve_wit_6 : mpz_add_partial_solve_wit_6.
Axiom proof_of_mpz_add_partial_solve_wit_7 : mpz_add_partial_solve_wit_7.
Axiom proof_of_mpz_add_partial_solve_wit_8 : mpz_add_partial_solve_wit_8.
Axiom proof_of_mpz_add_partial_solve_wit_9 : mpz_add_partial_solve_wit_9.
Axiom proof_of_mpz_add_partial_solve_wit_10 : mpz_add_partial_solve_wit_10.
Axiom proof_of_mpz_sub_safety_wit_1 : mpz_sub_safety_wit_1.
Axiom proof_of_mpz_sub_safety_wit_2 : mpz_sub_safety_wit_2.
Axiom proof_of_mpz_sub_safety_wit_3 : mpz_sub_safety_wit_3.
Axiom proof_of_mpz_sub_safety_wit_4 : mpz_sub_safety_wit_4.
Axiom proof_of_mpz_sub_safety_wit_5 : mpz_sub_safety_wit_5.
Axiom proof_of_mpz_sub_return_wit_1 : mpz_sub_return_wit_1.
Axiom proof_of_mpz_sub_return_wit_2 : mpz_sub_return_wit_2.
Axiom proof_of_mpz_sub_return_wit_3 : mpz_sub_return_wit_3.
Axiom proof_of_mpz_sub_return_wit_4 : mpz_sub_return_wit_4.
Axiom proof_of_mpz_sub_partial_solve_wit_1 : mpz_sub_partial_solve_wit_1.
Axiom proof_of_mpz_sub_partial_solve_wit_2 : mpz_sub_partial_solve_wit_2.
Axiom proof_of_mpz_sub_partial_solve_wit_3 : mpz_sub_partial_solve_wit_3.
Axiom proof_of_mpz_sub_partial_solve_wit_4 : mpz_sub_partial_solve_wit_4.
Axiom proof_of_mpz_sub_partial_solve_wit_5 : mpz_sub_partial_solve_wit_5.
Axiom proof_of_mpz_sub_partial_solve_wit_6 : mpz_sub_partial_solve_wit_6.
Axiom proof_of_mpz_sub_partial_solve_wit_7 : mpz_sub_partial_solve_wit_7.
Axiom proof_of_mpz_sub_partial_solve_wit_8 : mpz_sub_partial_solve_wit_8.
Axiom proof_of_mpz_sub_partial_solve_wit_9 : mpz_sub_partial_solve_wit_9.
Axiom proof_of_mpz_sub_partial_solve_wit_10 : mpz_sub_partial_solve_wit_10.

End VC_Correct.
