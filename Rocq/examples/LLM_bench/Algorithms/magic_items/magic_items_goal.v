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
Require Import SimpleC.EE.LLM_bench.Algorithms.magic_items.magic_items_lib.
Local Open Scope sac.

(*----- Function magic_items -----*)

Definition magic_items_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (1 <= c_pre)) (PreH4 : (c_pre <= 5000)) (PreH5 : (Forall (Z.le (1)) al )) (PreH6 : (Forall2 Z.le al bl )) (PreH7 : (Forall (Z.ge (10000)) bl )) ,
  ((( &( "s" ) )) # Int  |->_)
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition magic_items_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (1 <= c_pre)) (PreH4 : (c_pre <= 5000)) (PreH5 : (Forall (Z.le (1)) al )) (PreH6 : (Forall2 Z.le al bl )) (PreH7 : (Forall (Z.ge (10000)) bl )) ,
  ((( &( "t" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Int  |-> 0)
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition magic_items_safety_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (1 <= c_pre)) (PreH4 : (c_pre <= 5000)) (PreH5 : (Forall (Z.le (1)) al )) (PreH6 : (Forall2 Z.le al bl )) (PreH7 : (Forall (Z.ge (10000)) bl )) ,
  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Int  |-> 0)
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition magic_items_safety_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (1 <= c_pre)) (PreH4 : (c_pre <= 5000)) (PreH5 : (Forall (Z.le (1)) al )) (PreH6 : (Forall2 Z.le al bl )) (PreH7 : (Forall (Z.ge (10000)) bl )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |-> 0)
  **  ((( &( "t" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Int  |-> 0)
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition magic_items_safety_wit_5 := 
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (Forall (Z.le (1)) al )) (PreH9 : (Forall2 Z.le al bl )) (PreH10 : (Forall (Z.ge (10000)) bl )) (PreH11 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH12 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH13 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (0 <= t)) (PreH15 : (t <= (10000 * i ))) (PreH16 : (0 <= s)) (PreH17 : (s <= (10000 * i ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth i bl 0) - (Znth i al 0) ) - c_pre )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (Forall (Z.le (1)) al )) (PreH9 : (Forall2 Z.le al bl )) (PreH10 : (Forall (Z.ge (10000)) bl )) (PreH11 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH12 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH13 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (0 <= t)) (PreH15 : (t <= (10000 * i ))) (PreH16 : (0 <= s)) (PreH17 : (s <= (10000 * i ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth i bl 0) - (Znth i al 0) ) - c_pre )) ”
).

Definition magic_items_safety_wit_5_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (Forall (Z.le (1)) al )) (PreH9 : (Forall2 Z.le al bl )) (PreH10 : (Forall (Z.ge (10000)) bl )) (PreH11 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH12 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH13 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (0 <= t)) (PreH15 : (t <= (10000 * i ))) (PreH16 : (0 <= s)) (PreH17 : (s <= (10000 * i ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) <= INT_MAX) ”
.

Definition magic_items_safety_wit_5_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (Forall (Z.le (1)) al )) (PreH9 : (Forall2 Z.le al bl )) (PreH10 : (Forall (Z.ge (10000)) bl )) (PreH11 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH12 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH13 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (0 <= t)) (PreH15 : (t <= (10000 * i ))) (PreH16 : (0 <= s)) (PreH17 : (s <= (10000 * i ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ ((INT_MIN) <= (((Znth i bl 0) - (Znth i al 0) ) - c_pre )) ”
.

Definition magic_items_safety_wit_6 := 
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (Forall (Z.le (1)) al )) (PreH9 : (Forall2 Z.le al bl )) (PreH10 : (Forall (Z.ge (10000)) bl )) (PreH11 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH12 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH13 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (0 <= t)) (PreH15 : (t <= (10000 * i ))) (PreH16 : (0 <= s)) (PreH17 : (s <= (10000 * i ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ (((Znth i bl 0) - (Znth i al 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i bl 0) - (Znth i al 0) )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (Forall (Z.le (1)) al )) (PreH9 : (Forall2 Z.le al bl )) (PreH10 : (Forall (Z.ge (10000)) bl )) (PreH11 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH12 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH13 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (0 <= t)) (PreH15 : (t <= (10000 * i ))) (PreH16 : (0 <= s)) (PreH17 : (s <= (10000 * i ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ (((Znth i bl 0) - (Znth i al 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i bl 0) - (Znth i al 0) )) ”
).

Definition magic_items_safety_wit_6_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (Forall (Z.le (1)) al )) (PreH9 : (Forall2 Z.le al bl )) (PreH10 : (Forall (Z.ge (10000)) bl )) (PreH11 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH12 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH13 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (0 <= t)) (PreH15 : (t <= (10000 * i ))) (PreH16 : (0 <= s)) (PreH17 : (s <= (10000 * i ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ (((Znth i bl 0) - (Znth i al 0) ) <= INT_MAX) ”
.

Definition magic_items_safety_wit_6_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (Forall (Z.le (1)) al )) (PreH9 : (Forall2 Z.le al bl )) (PreH10 : (Forall (Z.ge (10000)) bl )) (PreH11 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH12 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH13 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (0 <= t)) (PreH15 : (t <= (10000 * i ))) (PreH16 : (0 <= s)) (PreH17 : (s <= (10000 * i ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ ((INT_MIN) <= ((Znth i bl 0) - (Znth i al 0) )) ”
.

Definition magic_items_safety_wit_7 := 
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (Forall (Z.le (1)) al )) (PreH9 : (Forall2 Z.le al bl )) (PreH10 : (Forall (Z.ge (10000)) bl )) (PreH11 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH12 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH13 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (0 <= t)) (PreH15 : (t <= (10000 * i ))) (PreH16 : (0 <= s)) (PreH17 : (s <= (10000 * i ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "d" ) )) # Int  |-> (((Znth i bl 0) - (Znth i al 0) ) - c_pre ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ ((t + (Znth i al 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (t + (Znth i al 0) )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (Forall (Z.le (1)) al )) (PreH9 : (Forall2 Z.le al bl )) (PreH10 : (Forall (Z.ge (10000)) bl )) (PreH11 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH12 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH13 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (0 <= t)) (PreH15 : (t <= (10000 * i ))) (PreH16 : (0 <= s)) (PreH17 : (s <= (10000 * i ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "d" ) )) # Int  |-> (((Znth i bl 0) - (Znth i al 0) ) - c_pre ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ ((t + (Znth i al 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (t + (Znth i al 0) )) ”
).

Definition magic_items_safety_wit_7_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (Forall (Z.le (1)) al )) (PreH9 : (Forall2 Z.le al bl )) (PreH10 : (Forall (Z.ge (10000)) bl )) (PreH11 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH12 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH13 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (0 <= t)) (PreH15 : (t <= (10000 * i ))) (PreH16 : (0 <= s)) (PreH17 : (s <= (10000 * i ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "d" ) )) # Int  |-> (((Znth i bl 0) - (Znth i al 0) ) - c_pre ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ ((t + (Znth i al 0) ) <= INT_MAX) ”
.

Definition magic_items_safety_wit_7_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (Forall (Z.le (1)) al )) (PreH9 : (Forall2 Z.le al bl )) (PreH10 : (Forall (Z.ge (10000)) bl )) (PreH11 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH12 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH13 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (0 <= t)) (PreH15 : (t <= (10000 * i ))) (PreH16 : (0 <= s)) (PreH17 : (s <= (10000 * i ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "d" ) )) # Int  |-> (((Znth i bl 0) - (Znth i al 0) ) - c_pre ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ ((INT_MIN) <= (t + (Znth i al 0) )) ”
.

Definition magic_items_safety_wit_8 := 
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (Forall (Z.le (1)) al )) (PreH9 : (Forall2 Z.le al bl )) (PreH10 : (Forall (Z.ge (10000)) bl )) (PreH11 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH12 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH13 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (0 <= t)) (PreH15 : (t <= (10000 * i ))) (PreH16 : (0 <= s)) (PreH17 : (s <= (10000 * i ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "d" ) )) # Int  |-> (((Znth i bl 0) - (Znth i al 0) ) - c_pre ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> (t + (Znth i al 0) ))
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ ((ans + (Znth i al 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ans + (Znth i al 0) )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (Forall (Z.le (1)) al )) (PreH9 : (Forall2 Z.le al bl )) (PreH10 : (Forall (Z.ge (10000)) bl )) (PreH11 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH12 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH13 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (0 <= t)) (PreH15 : (t <= (10000 * i ))) (PreH16 : (0 <= s)) (PreH17 : (s <= (10000 * i ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "d" ) )) # Int  |-> (((Znth i bl 0) - (Znth i al 0) ) - c_pre ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> (t + (Znth i al 0) ))
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ ((ans + (Znth i al 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ans + (Znth i al 0) )) ”
).

Definition magic_items_safety_wit_8_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (Forall (Z.le (1)) al )) (PreH9 : (Forall2 Z.le al bl )) (PreH10 : (Forall (Z.ge (10000)) bl )) (PreH11 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH12 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH13 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (0 <= t)) (PreH15 : (t <= (10000 * i ))) (PreH16 : (0 <= s)) (PreH17 : (s <= (10000 * i ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "d" ) )) # Int  |-> (((Znth i bl 0) - (Znth i al 0) ) - c_pre ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> (t + (Znth i al 0) ))
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ ((ans + (Znth i al 0) ) <= INT_MAX) ”
.

Definition magic_items_safety_wit_8_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (Forall (Z.le (1)) al )) (PreH9 : (Forall2 Z.le al bl )) (PreH10 : (Forall (Z.ge (10000)) bl )) (PreH11 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH12 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH13 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (0 <= t)) (PreH15 : (t <= (10000 * i ))) (PreH16 : (0 <= s)) (PreH17 : (s <= (10000 * i ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "d" ) )) # Int  |-> (((Znth i bl 0) - (Znth i al 0) ) - c_pre ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> (t + (Znth i al 0) ))
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ ((INT_MIN) <= (ans + (Znth i al 0) )) ”
.

Definition magic_items_safety_wit_9 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (Forall (Z.le (1)) al )) (PreH9 : (Forall2 Z.le al bl )) (PreH10 : (Forall (Z.ge (10000)) bl )) (PreH11 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH12 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH13 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (0 <= t)) (PreH15 : (t <= (10000 * i ))) (PreH16 : (0 <= s)) (PreH17 : (s <= (10000 * i ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "d" ) )) # Int  |-> (((Znth i bl 0) - (Znth i al 0) ) - c_pre ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> (t + (Znth i al 0) ))
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "ans" ) )) # Int  |-> (ans + (Znth i al 0) ))
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition magic_items_safety_wit_10 := 
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) > 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall (Z.le (1)) al )) (PreH10 : (Forall2 Z.le al bl )) (PreH11 : (Forall (Z.ge (10000)) bl )) (PreH12 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH13 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (0 <= t)) (PreH16 : (t <= (10000 * i ))) (PreH17 : (0 <= s)) (PreH18 : (s <= (10000 * i ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "d" ) )) # Int  |-> (((Znth i bl 0) - (Znth i al 0) ) - c_pre ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> (t + (Znth i al 0) ))
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "ans" ) )) # Int  |-> (ans + (Znth i al 0) ))
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ (((ans + (Znth i al 0) ) + (((Znth i bl 0) - (Znth i al 0) ) - c_pre ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((ans + (Znth i al 0) ) + (((Znth i bl 0) - (Znth i al 0) ) - c_pre ) )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) > 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall (Z.le (1)) al )) (PreH10 : (Forall2 Z.le al bl )) (PreH11 : (Forall (Z.ge (10000)) bl )) (PreH12 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH13 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (0 <= t)) (PreH16 : (t <= (10000 * i ))) (PreH17 : (0 <= s)) (PreH18 : (s <= (10000 * i ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "d" ) )) # Int  |-> (((Znth i bl 0) - (Znth i al 0) ) - c_pre ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> (t + (Znth i al 0) ))
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "ans" ) )) # Int  |-> (ans + (Znth i al 0) ))
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ (((ans + (Znth i al 0) ) + (((Znth i bl 0) - (Znth i al 0) ) - c_pre ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((ans + (Znth i al 0) ) + (((Znth i bl 0) - (Znth i al 0) ) - c_pre ) )) ”
).

Definition magic_items_safety_wit_10_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) > 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall (Z.le (1)) al )) (PreH10 : (Forall2 Z.le al bl )) (PreH11 : (Forall (Z.ge (10000)) bl )) (PreH12 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH13 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (0 <= t)) (PreH16 : (t <= (10000 * i ))) (PreH17 : (0 <= s)) (PreH18 : (s <= (10000 * i ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "d" ) )) # Int  |-> (((Znth i bl 0) - (Znth i al 0) ) - c_pre ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> (t + (Znth i al 0) ))
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "ans" ) )) # Int  |-> (ans + (Znth i al 0) ))
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ (((ans + (Znth i al 0) ) + (((Znth i bl 0) - (Znth i al 0) ) - c_pre ) ) <= INT_MAX) ”
.

Definition magic_items_safety_wit_10_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) > 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall (Z.le (1)) al )) (PreH10 : (Forall2 Z.le al bl )) (PreH11 : (Forall (Z.ge (10000)) bl )) (PreH12 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH13 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (0 <= t)) (PreH16 : (t <= (10000 * i ))) (PreH17 : (0 <= s)) (PreH18 : (s <= (10000 * i ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "d" ) )) # Int  |-> (((Znth i bl 0) - (Znth i al 0) ) - c_pre ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> (t + (Znth i al 0) ))
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "ans" ) )) # Int  |-> (ans + (Znth i al 0) ))
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ ((INT_MIN) <= ((ans + (Znth i al 0) ) + (((Znth i bl 0) - (Znth i al 0) ) - c_pre ) )) ”
.

Definition magic_items_safety_wit_11 := 
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) <= 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall (Z.le (1)) al )) (PreH10 : (Forall2 Z.le al bl )) (PreH11 : (Forall (Z.ge (10000)) bl )) (PreH12 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH13 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (0 <= t)) (PreH16 : (t <= (10000 * i ))) (PreH17 : (0 <= s)) (PreH18 : (s <= (10000 * i ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "d" ) )) # Int  |-> (((Znth i bl 0) - (Znth i al 0) ) - c_pre ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> (t + (Znth i al 0) ))
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "ans" ) )) # Int  |-> (ans + (Znth i al 0) ))
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ ((s + (Znth i al 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (s + (Znth i al 0) )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) <= 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall (Z.le (1)) al )) (PreH10 : (Forall2 Z.le al bl )) (PreH11 : (Forall (Z.ge (10000)) bl )) (PreH12 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH13 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (0 <= t)) (PreH16 : (t <= (10000 * i ))) (PreH17 : (0 <= s)) (PreH18 : (s <= (10000 * i ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "d" ) )) # Int  |-> (((Znth i bl 0) - (Znth i al 0) ) - c_pre ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> (t + (Znth i al 0) ))
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "ans" ) )) # Int  |-> (ans + (Znth i al 0) ))
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ ((s + (Znth i al 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (s + (Znth i al 0) )) ”
).

Definition magic_items_safety_wit_11_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) <= 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall (Z.le (1)) al )) (PreH10 : (Forall2 Z.le al bl )) (PreH11 : (Forall (Z.ge (10000)) bl )) (PreH12 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH13 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (0 <= t)) (PreH16 : (t <= (10000 * i ))) (PreH17 : (0 <= s)) (PreH18 : (s <= (10000 * i ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "d" ) )) # Int  |-> (((Znth i bl 0) - (Znth i al 0) ) - c_pre ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> (t + (Znth i al 0) ))
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "ans" ) )) # Int  |-> (ans + (Znth i al 0) ))
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ ((s + (Znth i al 0) ) <= INT_MAX) ”
.

Definition magic_items_safety_wit_11_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) <= 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall (Z.le (1)) al )) (PreH10 : (Forall2 Z.le al bl )) (PreH11 : (Forall (Z.ge (10000)) bl )) (PreH12 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH13 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (0 <= t)) (PreH16 : (t <= (10000 * i ))) (PreH17 : (0 <= s)) (PreH18 : (s <= (10000 * i ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "d" ) )) # Int  |-> (((Znth i bl 0) - (Znth i al 0) ) - c_pre ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> (t + (Znth i al 0) ))
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "ans" ) )) # Int  |-> (ans + (Znth i al 0) ))
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ ((INT_MIN) <= (s + (Znth i al 0) )) ”
.

Definition magic_items_safety_wit_12 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) > 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall (Z.le (1)) al )) (PreH10 : (Forall2 Z.le al bl )) (PreH11 : (Forall (Z.ge (10000)) bl )) (PreH12 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH13 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (0 <= t)) (PreH16 : (t <= (10000 * i ))) (PreH17 : (0 <= s)) (PreH18 : (s <= (10000 * i ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> (t + (Znth i al 0) ))
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "ans" ) )) # Int  |-> ((ans + (Znth i al 0) ) + (((Znth i bl 0) - (Znth i al 0) ) - c_pre ) ))
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition magic_items_safety_wit_13 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) <= 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall (Z.le (1)) al )) (PreH10 : (Forall2 Z.le al bl )) (PreH11 : (Forall (Z.ge (10000)) bl )) (PreH12 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH13 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (0 <= t)) (PreH16 : (t <= (10000 * i ))) (PreH17 : (0 <= s)) (PreH18 : (s <= (10000 * i ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> (t + (Znth i al 0) ))
  **  ((( &( "s" ) )) # Int  |-> (s + (Znth i al 0) ))
  **  ((( &( "ans" ) )) # Int  |-> (ans + (Znth i al 0) ))
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition magic_items_safety_wit_14 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : (s < c_pre)) (PreH2 : (t >= c_pre)) (PreH3 : (i >= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 5000)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (Forall (Z.le (1)) al )) (PreH11 : (Forall2 Z.le al bl )) (PreH12 : (Forall (Z.ge (10000)) bl )) (PreH13 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH14 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH16 : (0 <= t)) (PreH17 : (t <= (10000 * i ))) (PreH18 : (0 <= s)) (PreH19 : (s <= (10000 * i ))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= (10000 * i ))) ,
  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ ((c_pre - s ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (c_pre - s )) ”
.

Definition magic_items_safety_wit_15 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : (s < c_pre)) (PreH2 : (t >= c_pre)) (PreH3 : (i >= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 5000)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (Forall (Z.le (1)) al )) (PreH11 : (Forall2 Z.le al bl )) (PreH12 : (Forall (Z.ge (10000)) bl )) (PreH13 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH14 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH16 : (0 <= t)) (PreH17 : (t <= (10000 * i ))) (PreH18 : (0 <= s)) (PreH19 : (s <= (10000 * i ))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= (10000 * i ))) ,
  ((( &( "k" ) )) # Int  |-> (c_pre - s ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition magic_items_safety_wit_16 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : (s < c_pre)) (PreH2 : (t >= c_pre)) (PreH3 : (i >= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 5000)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (Forall (Z.le (1)) al )) (PreH11 : (Forall2 Z.le al bl )) (PreH12 : (Forall (Z.ge (10000)) bl )) (PreH13 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH14 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH16 : (0 <= t)) (PreH17 : (t <= (10000 * i ))) (PreH18 : (0 <= s)) (PreH19 : (s <= (10000 * i ))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= (10000 * i ))) ,
  ((( &( "k" ) )) # Int  |-> (c_pre - s ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition magic_items_safety_wit_17 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : (s < c_pre)) (PreH2 : (t >= c_pre)) (PreH3 : (i >= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 5000)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (Forall (Z.le (1)) al )) (PreH11 : (Forall2 Z.le al bl )) (PreH12 : (Forall (Z.ge (10000)) bl )) (PreH13 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH14 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH16 : (0 <= t)) (PreH17 : (t <= (10000 * i ))) (PreH18 : (0 <= s)) (PreH19 : (s <= (10000 * i ))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= (10000 * i ))) ,
  ((( &( "j" ) )) # Int  |->_)
  **  (((( &( "dp" ) ) + (0 * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.undef_seg ( &( "dp" ) ) 1 5001 )
  **  ((( &( "k" ) )) # Int  |-> (c_pre - s ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition magic_items_safety_wit_18 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (j: Z) (k: Z) (PreH1 : (j <= k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= (k + 1 ))) (PreH10 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH11 : (c_pre <= (ListLib.sum (al)))) (PreH12 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH13 : (0 <= ans)) (PreH14 : (ans <= 10000000)) (PreH15 : (Forall (Z.le (1)) al )) (PreH16 : (Forall2 Z.le al bl )) (PreH17 : (Forall (Z.ge (10000)) bl )) (PreH18 : ((Znth (0) (dl) (0)) = 0)) (PreH19 : (Forall (eq (10000001)) (sublist (1) (j) (dl)) )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.seg ( &( "dp" ) ) 0 j dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) j 5001 )
|--
  “ (10000001 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10000001) ”
.

Definition magic_items_safety_wit_19 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (j: Z) (k: Z) (PreH1 : (j <= k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= (k + 1 ))) (PreH10 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH11 : (c_pre <= (ListLib.sum (al)))) (PreH12 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH13 : (0 <= ans)) (PreH14 : (ans <= 10000000)) (PreH15 : (Forall (Z.le (1)) al )) (PreH16 : (Forall2 Z.le al bl )) (PreH17 : (Forall (Z.ge (10000)) bl )) (PreH18 : ((Znth (0) (dl) (0)) = 0)) (PreH19 : (Forall (eq (10000001)) (sublist (1) (j) (dl)) )) ,
  (IntArray.seg ( &( "dp" ) ) 0 (j + 1 ) (app (dl) ((cons (10000001) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "dp" ) ) (j + 1 ) 5001 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition magic_items_safety_wit_20 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (j: Z) (k: Z) (PreH1 : (j > k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= (k + 1 ))) (PreH10 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH11 : (c_pre <= (ListLib.sum (al)))) (PreH12 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH13 : (0 <= ans)) (PreH14 : (ans <= 10000000)) (PreH15 : (Forall (Z.le (1)) al )) (PreH16 : (Forall2 Z.le al bl )) (PreH17 : (Forall (Z.ge (10000)) bl )) (PreH18 : ((Znth (0) (dl) (0)) = 0)) (PreH19 : (Forall (eq (10000001)) (sublist (1) (j) (dl)) )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.seg ( &( "dp" ) ) 0 j dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) j 5001 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition magic_items_safety_wit_21 := 
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH11 : (c_pre <= (ListLib.sum (al)))) (PreH12 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH13 : (0 <= ans)) (PreH14 : (ans <= 10000000)) (PreH15 : (Forall (Z.le (1)) al )) (PreH16 : (Forall2 Z.le al bl )) (PreH17 : (Forall (Z.ge (10000)) bl )) (PreH18 : (Forall (Z.le (0)) dl )) (PreH19 : (Forall (Z.ge (10000001)) dl )) (PreH20 : forall (q: Z) , (((0 <= q) /\ (q <= k)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth i bl 0) - (Znth i al 0) ) - c_pre )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH11 : (c_pre <= (ListLib.sum (al)))) (PreH12 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH13 : (0 <= ans)) (PreH14 : (ans <= 10000000)) (PreH15 : (Forall (Z.le (1)) al )) (PreH16 : (Forall2 Z.le al bl )) (PreH17 : (Forall (Z.ge (10000)) bl )) (PreH18 : (Forall (Z.le (0)) dl )) (PreH19 : (Forall (Z.ge (10000001)) dl )) (PreH20 : forall (q: Z) , (((0 <= q) /\ (q <= k)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth i bl 0) - (Znth i al 0) ) - c_pre )) ”
).

Definition magic_items_safety_wit_21_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH11 : (c_pre <= (ListLib.sum (al)))) (PreH12 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH13 : (0 <= ans)) (PreH14 : (ans <= 10000000)) (PreH15 : (Forall (Z.le (1)) al )) (PreH16 : (Forall2 Z.le al bl )) (PreH17 : (Forall (Z.ge (10000)) bl )) (PreH18 : (Forall (Z.le (0)) dl )) (PreH19 : (Forall (Z.ge (10000001)) dl )) (PreH20 : forall (q: Z) , (((0 <= q) /\ (q <= k)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) <= INT_MAX) ”
.

Definition magic_items_safety_wit_21_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH11 : (c_pre <= (ListLib.sum (al)))) (PreH12 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH13 : (0 <= ans)) (PreH14 : (ans <= 10000000)) (PreH15 : (Forall (Z.le (1)) al )) (PreH16 : (Forall2 Z.le al bl )) (PreH17 : (Forall (Z.ge (10000)) bl )) (PreH18 : (Forall (Z.le (0)) dl )) (PreH19 : (Forall (Z.ge (10000001)) dl )) (PreH20 : forall (q: Z) , (((0 <= q) /\ (q <= k)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ ((INT_MIN) <= (((Znth i bl 0) - (Znth i al 0) ) - c_pre )) ”
.

Definition magic_items_safety_wit_22 := 
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH11 : (c_pre <= (ListLib.sum (al)))) (PreH12 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH13 : (0 <= ans)) (PreH14 : (ans <= 10000000)) (PreH15 : (Forall (Z.le (1)) al )) (PreH16 : (Forall2 Z.le al bl )) (PreH17 : (Forall (Z.ge (10000)) bl )) (PreH18 : (Forall (Z.le (0)) dl )) (PreH19 : (Forall (Z.ge (10000001)) dl )) (PreH20 : forall (q: Z) , (((0 <= q) /\ (q <= k)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ (((Znth i bl 0) - (Znth i al 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i bl 0) - (Znth i al 0) )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH11 : (c_pre <= (ListLib.sum (al)))) (PreH12 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH13 : (0 <= ans)) (PreH14 : (ans <= 10000000)) (PreH15 : (Forall (Z.le (1)) al )) (PreH16 : (Forall2 Z.le al bl )) (PreH17 : (Forall (Z.ge (10000)) bl )) (PreH18 : (Forall (Z.le (0)) dl )) (PreH19 : (Forall (Z.ge (10000001)) dl )) (PreH20 : forall (q: Z) , (((0 <= q) /\ (q <= k)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ (((Znth i bl 0) - (Znth i al 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i bl 0) - (Znth i al 0) )) ”
).

Definition magic_items_safety_wit_22_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH11 : (c_pre <= (ListLib.sum (al)))) (PreH12 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH13 : (0 <= ans)) (PreH14 : (ans <= 10000000)) (PreH15 : (Forall (Z.le (1)) al )) (PreH16 : (Forall2 Z.le al bl )) (PreH17 : (Forall (Z.ge (10000)) bl )) (PreH18 : (Forall (Z.le (0)) dl )) (PreH19 : (Forall (Z.ge (10000001)) dl )) (PreH20 : forall (q: Z) , (((0 <= q) /\ (q <= k)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ (((Znth i bl 0) - (Znth i al 0) ) <= INT_MAX) ”
.

Definition magic_items_safety_wit_22_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH11 : (c_pre <= (ListLib.sum (al)))) (PreH12 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH13 : (0 <= ans)) (PreH14 : (ans <= 10000000)) (PreH15 : (Forall (Z.le (1)) al )) (PreH16 : (Forall2 Z.le al bl )) (PreH17 : (Forall (Z.ge (10000)) bl )) (PreH18 : (Forall (Z.le (0)) dl )) (PreH19 : (Forall (Z.ge (10000001)) dl )) (PreH20 : forall (q: Z) , (((0 <= q) /\ (q <= k)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ ((INT_MIN) <= ((Znth i bl 0) - (Znth i al 0) )) ”
.

Definition magic_items_safety_wit_23 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH11 : (c_pre <= (ListLib.sum (al)))) (PreH12 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH13 : (0 <= ans)) (PreH14 : (ans <= 10000000)) (PreH15 : (Forall (Z.le (1)) al )) (PreH16 : (Forall2 Z.le al bl )) (PreH17 : (Forall (Z.ge (10000)) bl )) (PreH18 : (Forall (Z.le (0)) dl )) (PreH19 : (Forall (Z.ge (10000001)) dl )) (PreH20 : forall (q: Z) , (((0 <= q) /\ (q <= k)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "d" ) )) # Int  |-> (((Znth i bl 0) - (Znth i al 0) ) - c_pre ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition magic_items_safety_wit_24 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (1 <= c_pre)) (PreH4 : (c_pre <= 5000)) (PreH5 : (1 <= k)) (PreH6 : (k <= c_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= k)) (PreH11 : (1 <= (Znth i al 0))) (PreH12 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH13 : (0 < d)) (PreH14 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH15 : (c_pre <= (ListLib.sum (al)))) (PreH16 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH17 : (0 <= ans)) (PreH18 : (ans <= 10000000)) (PreH19 : (Forall (Z.le (1)) al )) (PreH20 : (Forall2 Z.le al bl )) (PreH21 : (Forall (Z.ge (10000)) bl )) (PreH22 : (Forall (Z.le (0)) dl )) (PreH23 : (Forall (Z.ge (10000001)) dl )) (PreH24 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) (PreH25 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) ))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition magic_items_safety_wit_25 := 
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (j > 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= k)) (PreH12 : (1 <= (Znth i al 0))) (PreH13 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH14 : (0 < d)) (PreH15 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH16 : (c_pre <= (ListLib.sum (al)))) (PreH17 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= 10000000)) (PreH20 : (Forall (Z.le (1)) al )) (PreH21 : (Forall2 Z.le al bl )) (PreH22 : (Forall (Z.ge (10000)) bl )) (PreH23 : (Forall (Z.le (0)) dl )) (PreH24 : (Forall (Z.ge (10000001)) dl )) (PreH25 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) (PreH26 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) ))) ,
  (IntArray.full a_pre n_pre al )
  **  ((( &( "r" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ ((j - (Znth i al 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - (Znth i al 0) )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (j > 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= k)) (PreH12 : (1 <= (Znth i al 0))) (PreH13 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH14 : (0 < d)) (PreH15 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH16 : (c_pre <= (ListLib.sum (al)))) (PreH17 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= 10000000)) (PreH20 : (Forall (Z.le (1)) al )) (PreH21 : (Forall2 Z.le al bl )) (PreH22 : (Forall (Z.ge (10000)) bl )) (PreH23 : (Forall (Z.le (0)) dl )) (PreH24 : (Forall (Z.ge (10000001)) dl )) (PreH25 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) (PreH26 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) ))) ,
  (IntArray.full a_pre n_pre al )
  **  ((( &( "r" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ ((j - (Znth i al 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - (Znth i al 0) )) ”
).

Definition magic_items_safety_wit_25_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (j > 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= k)) (PreH12 : (1 <= (Znth i al 0))) (PreH13 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH14 : (0 < d)) (PreH15 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH16 : (c_pre <= (ListLib.sum (al)))) (PreH17 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= 10000000)) (PreH20 : (Forall (Z.le (1)) al )) (PreH21 : (Forall2 Z.le al bl )) (PreH22 : (Forall (Z.ge (10000)) bl )) (PreH23 : (Forall (Z.le (0)) dl )) (PreH24 : (Forall (Z.ge (10000001)) dl )) (PreH25 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) (PreH26 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) ))) ,
  (IntArray.full a_pre n_pre al )
  **  ((( &( "r" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ ((j - (Znth i al 0) ) <= INT_MAX) ”
.

Definition magic_items_safety_wit_25_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (j > 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= k)) (PreH12 : (1 <= (Znth i al 0))) (PreH13 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH14 : (0 < d)) (PreH15 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH16 : (c_pre <= (ListLib.sum (al)))) (PreH17 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= 10000000)) (PreH20 : (Forall (Z.le (1)) al )) (PreH21 : (Forall2 Z.le al bl )) (PreH22 : (Forall (Z.ge (10000)) bl )) (PreH23 : (Forall (Z.le (0)) dl )) (PreH24 : (Forall (Z.ge (10000001)) dl )) (PreH25 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) (PreH26 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) ))) ,
  (IntArray.full a_pre n_pre al )
  **  ((( &( "r" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ ((INT_MIN) <= (j - (Znth i al 0) )) ”
.

Definition magic_items_safety_wit_26 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (j > 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= k)) (PreH12 : (1 <= (Znth i al 0))) (PreH13 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH14 : (0 < d)) (PreH15 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH16 : (c_pre <= (ListLib.sum (al)))) (PreH17 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= 10000000)) (PreH20 : (Forall (Z.le (1)) al )) (PreH21 : (Forall2 Z.le al bl )) (PreH22 : (Forall (Z.ge (10000)) bl )) (PreH23 : (Forall (Z.le (0)) dl )) (PreH24 : (Forall (Z.ge (10000001)) dl )) (PreH25 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) (PreH26 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) ))) ,
  (IntArray.full a_pre n_pre al )
  **  ((( &( "r" ) )) # Int  |-> (j - (Znth i al 0) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition magic_items_safety_wit_27 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : ((j - (Znth i al 0) ) < 0)) (PreH2 : (j > 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (1 <= k)) (PreH8 : (k <= c_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= k)) (PreH13 : (1 <= (Znth i al 0))) (PreH14 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH15 : (0 < d)) (PreH16 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH17 : (c_pre <= (ListLib.sum (al)))) (PreH18 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= 10000000)) (PreH21 : (Forall (Z.le (1)) al )) (PreH22 : (Forall2 Z.le al bl )) (PreH23 : (Forall (Z.ge (10000)) bl )) (PreH24 : (Forall (Z.le (0)) dl )) (PreH25 : (Forall (Z.ge (10000001)) dl )) (PreH26 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) (PreH27 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) ))) ,
  (IntArray.full a_pre n_pre al )
  **  ((( &( "r" ) )) # Int  |-> (j - (Znth i al 0) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition magic_items_safety_wit_28 := 
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : ((j - (Znth i al 0) ) < 0)) (PreH2 : (j > 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (1 <= k)) (PreH8 : (k <= c_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= k)) (PreH13 : (1 <= (Znth i al 0))) (PreH14 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH15 : (0 < d)) (PreH16 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH17 : (c_pre <= (ListLib.sum (al)))) (PreH18 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= 10000000)) (PreH21 : (Forall (Z.le (1)) al )) (PreH22 : (Forall2 Z.le al bl )) (PreH23 : (Forall (Z.ge (10000)) bl )) (PreH24 : (Forall (Z.le (0)) dl )) (PreH25 : (Forall (Z.ge (10000001)) dl )) (PreH26 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) (PreH27 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) ))) ,
  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  ((( &( "v" ) )) # Int  |->_)
  **  (IntArray.full a_pre n_pre al )
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ (((Znth 0 dl 0) + d ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth 0 dl 0) + d )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : ((j - (Znth i al 0) ) < 0)) (PreH2 : (j > 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (1 <= k)) (PreH8 : (k <= c_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= k)) (PreH13 : (1 <= (Znth i al 0))) (PreH14 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH15 : (0 < d)) (PreH16 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH17 : (c_pre <= (ListLib.sum (al)))) (PreH18 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= 10000000)) (PreH21 : (Forall (Z.le (1)) al )) (PreH22 : (Forall2 Z.le al bl )) (PreH23 : (Forall (Z.ge (10000)) bl )) (PreH24 : (Forall (Z.le (0)) dl )) (PreH25 : (Forall (Z.ge (10000001)) dl )) (PreH26 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) (PreH27 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) ))) ,
  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  ((( &( "v" ) )) # Int  |->_)
  **  (IntArray.full a_pre n_pre al )
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ (((Znth 0 dl 0) + d ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth 0 dl 0) + d )) ”
).

Definition magic_items_safety_wit_28_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : ((j - (Znth i al 0) ) < 0)) (PreH2 : (j > 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (1 <= k)) (PreH8 : (k <= c_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= k)) (PreH13 : (1 <= (Znth i al 0))) (PreH14 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH15 : (0 < d)) (PreH16 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH17 : (c_pre <= (ListLib.sum (al)))) (PreH18 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= 10000000)) (PreH21 : (Forall (Z.le (1)) al )) (PreH22 : (Forall2 Z.le al bl )) (PreH23 : (Forall (Z.ge (10000)) bl )) (PreH24 : (Forall (Z.le (0)) dl )) (PreH25 : (Forall (Z.ge (10000001)) dl )) (PreH26 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) (PreH27 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) ))) ,
  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  ((( &( "v" ) )) # Int  |->_)
  **  (IntArray.full a_pre n_pre al )
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ (((Znth 0 dl 0) + d ) <= INT_MAX) ”
.

Definition magic_items_safety_wit_28_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : ((j - (Znth i al 0) ) < 0)) (PreH2 : (j > 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (1 <= k)) (PreH8 : (k <= c_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= k)) (PreH13 : (1 <= (Znth i al 0))) (PreH14 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH15 : (0 < d)) (PreH16 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH17 : (c_pre <= (ListLib.sum (al)))) (PreH18 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= 10000000)) (PreH21 : (Forall (Z.le (1)) al )) (PreH22 : (Forall2 Z.le al bl )) (PreH23 : (Forall (Z.ge (10000)) bl )) (PreH24 : (Forall (Z.le (0)) dl )) (PreH25 : (Forall (Z.ge (10000001)) dl )) (PreH26 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) (PreH27 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) ))) ,
  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  ((( &( "v" ) )) # Int  |->_)
  **  (IntArray.full a_pre n_pre al )
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ ((INT_MIN) <= ((Znth 0 dl 0) + d )) ”
.

Definition magic_items_safety_wit_29 := 
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : ((j - (Znth i al 0) ) >= 0)) (PreH2 : (j > 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (1 <= k)) (PreH8 : (k <= c_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= k)) (PreH13 : (1 <= (Znth i al 0))) (PreH14 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH15 : (0 < d)) (PreH16 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH17 : (c_pre <= (ListLib.sum (al)))) (PreH18 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= 10000000)) (PreH21 : (Forall (Z.le (1)) al )) (PreH22 : (Forall2 Z.le al bl )) (PreH23 : (Forall (Z.ge (10000)) bl )) (PreH24 : (Forall (Z.le (0)) dl )) (PreH25 : (Forall (Z.ge (10000001)) dl )) (PreH26 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) (PreH27 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) ))) ,
  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  ((( &( "v" ) )) # Int  |->_)
  **  (IntArray.full a_pre n_pre al )
  **  ((( &( "r" ) )) # Int  |-> (j - (Znth i al 0) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ (((Znth (j - (Znth i al 0) ) dl 0) + d ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (j - (Znth i al 0) ) dl 0) + d )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : ((j - (Znth i al 0) ) >= 0)) (PreH2 : (j > 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (1 <= k)) (PreH8 : (k <= c_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= k)) (PreH13 : (1 <= (Znth i al 0))) (PreH14 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH15 : (0 < d)) (PreH16 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH17 : (c_pre <= (ListLib.sum (al)))) (PreH18 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= 10000000)) (PreH21 : (Forall (Z.le (1)) al )) (PreH22 : (Forall2 Z.le al bl )) (PreH23 : (Forall (Z.ge (10000)) bl )) (PreH24 : (Forall (Z.le (0)) dl )) (PreH25 : (Forall (Z.ge (10000001)) dl )) (PreH26 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) (PreH27 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) ))) ,
  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  ((( &( "v" ) )) # Int  |->_)
  **  (IntArray.full a_pre n_pre al )
  **  ((( &( "r" ) )) # Int  |-> (j - (Znth i al 0) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ (((Znth (j - (Znth i al 0) ) dl 0) + d ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (j - (Znth i al 0) ) dl 0) + d )) ”
).

Definition magic_items_safety_wit_29_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : ((j - (Znth i al 0) ) >= 0)) (PreH2 : (j > 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (1 <= k)) (PreH8 : (k <= c_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= k)) (PreH13 : (1 <= (Znth i al 0))) (PreH14 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH15 : (0 < d)) (PreH16 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH17 : (c_pre <= (ListLib.sum (al)))) (PreH18 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= 10000000)) (PreH21 : (Forall (Z.le (1)) al )) (PreH22 : (Forall2 Z.le al bl )) (PreH23 : (Forall (Z.ge (10000)) bl )) (PreH24 : (Forall (Z.le (0)) dl )) (PreH25 : (Forall (Z.ge (10000001)) dl )) (PreH26 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) (PreH27 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) ))) ,
  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  ((( &( "v" ) )) # Int  |->_)
  **  (IntArray.full a_pre n_pre al )
  **  ((( &( "r" ) )) # Int  |-> (j - (Znth i al 0) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ (((Znth (j - (Znth i al 0) ) dl 0) + d ) <= INT_MAX) ”
.

Definition magic_items_safety_wit_29_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : ((j - (Znth i al 0) ) >= 0)) (PreH2 : (j > 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (1 <= k)) (PreH8 : (k <= c_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= k)) (PreH13 : (1 <= (Znth i al 0))) (PreH14 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH15 : (0 < d)) (PreH16 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH17 : (c_pre <= (ListLib.sum (al)))) (PreH18 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= 10000000)) (PreH21 : (Forall (Z.le (1)) al )) (PreH22 : (Forall2 Z.le al bl )) (PreH23 : (Forall (Z.ge (10000)) bl )) (PreH24 : (Forall (Z.le (0)) dl )) (PreH25 : (Forall (Z.ge (10000001)) dl )) (PreH26 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) (PreH27 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) ))) ,
  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  ((( &( "v" ) )) # Int  |->_)
  **  (IntArray.full a_pre n_pre al )
  **  ((( &( "r" ) )) # Int  |-> (j - (Znth i al 0) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ ((INT_MIN) <= ((Znth (j - (Znth i al 0) ) dl 0) + d )) ”
.

Definition magic_items_safety_wit_30 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (((Znth 0 dl 0) + d ) < (Znth j dl 0))) (PreH2 : ((j - (Znth i al 0) ) < 0)) (PreH3 : (j > 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 5000)) (PreH8 : (1 <= k)) (PreH9 : (k <= c_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= k)) (PreH14 : (1 <= (Znth i al 0))) (PreH15 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH16 : (0 < d)) (PreH17 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH18 : (c_pre <= (ListLib.sum (al)))) (PreH19 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= 10000000)) (PreH22 : (Forall (Z.le (1)) al )) (PreH23 : (Forall2 Z.le al bl )) (PreH24 : (Forall (Z.ge (10000)) bl )) (PreH25 : (Forall (Z.le (0)) dl )) (PreH26 : (Forall (Z.ge (10000001)) dl )) (PreH27 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) (PreH28 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) ))) ,
  (IntArray.full ( &( "dp" ) ) (k + 1 ) (replace_Znth (j) (((Znth 0 dl 0) + d )) (dl)) )
  **  (IntArray.full a_pre n_pre al )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition magic_items_safety_wit_31 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (((Znth (j - (Znth i al 0) ) dl 0) + d ) < (Znth j dl 0))) (PreH2 : ((j - (Znth i al 0) ) >= 0)) (PreH3 : (j > 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 5000)) (PreH8 : (1 <= k)) (PreH9 : (k <= c_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= k)) (PreH14 : (1 <= (Znth i al 0))) (PreH15 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH16 : (0 < d)) (PreH17 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH18 : (c_pre <= (ListLib.sum (al)))) (PreH19 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= 10000000)) (PreH22 : (Forall (Z.le (1)) al )) (PreH23 : (Forall2 Z.le al bl )) (PreH24 : (Forall (Z.ge (10000)) bl )) (PreH25 : (Forall (Z.le (0)) dl )) (PreH26 : (Forall (Z.ge (10000001)) dl )) (PreH27 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) (PreH28 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) ))) ,
  (IntArray.full ( &( "dp" ) ) (k + 1 ) (replace_Znth (j) (((Znth (j - (Znth i al 0) ) dl 0) + d )) (dl)) )
  **  (IntArray.full a_pre n_pre al )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition magic_items_safety_wit_32 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (((Znth 0 dl 0) + d ) >= (Znth j dl 0))) (PreH2 : ((j - (Znth i al 0) ) < 0)) (PreH3 : (j > 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 5000)) (PreH8 : (1 <= k)) (PreH9 : (k <= c_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= k)) (PreH14 : (1 <= (Znth i al 0))) (PreH15 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH16 : (0 < d)) (PreH17 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH18 : (c_pre <= (ListLib.sum (al)))) (PreH19 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= 10000000)) (PreH22 : (Forall (Z.le (1)) al )) (PreH23 : (Forall2 Z.le al bl )) (PreH24 : (Forall (Z.ge (10000)) bl )) (PreH25 : (Forall (Z.le (0)) dl )) (PreH26 : (Forall (Z.ge (10000001)) dl )) (PreH27 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) (PreH28 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) ))) ,
  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.full a_pre n_pre al )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition magic_items_safety_wit_33 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (((Znth (j - (Znth i al 0) ) dl 0) + d ) >= (Znth j dl 0))) (PreH2 : ((j - (Znth i al 0) ) >= 0)) (PreH3 : (j > 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 5000)) (PreH8 : (1 <= k)) (PreH9 : (k <= c_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= k)) (PreH14 : (1 <= (Znth i al 0))) (PreH15 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH16 : (0 < d)) (PreH17 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH18 : (c_pre <= (ListLib.sum (al)))) (PreH19 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= 10000000)) (PreH22 : (Forall (Z.le (1)) al )) (PreH23 : (Forall2 Z.le al bl )) (PreH24 : (Forall (Z.ge (10000)) bl )) (PreH25 : (Forall (Z.le (0)) dl )) (PreH26 : (Forall (Z.ge (10000001)) dl )) (PreH27 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) (PreH28 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) ))) ,
  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.full a_pre n_pre al )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition magic_items_safety_wit_34 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (j <= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= k)) (PreH12 : (1 <= (Znth i al 0))) (PreH13 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH14 : (0 < d)) (PreH15 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH16 : (c_pre <= (ListLib.sum (al)))) (PreH17 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= 10000000)) (PreH20 : (Forall (Z.le (1)) al )) (PreH21 : (Forall2 Z.le al bl )) (PreH22 : (Forall (Z.ge (10000)) bl )) (PreH23 : (Forall (Z.le (0)) dl )) (PreH24 : (Forall (Z.ge (10000001)) dl )) (PreH25 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) (PreH26 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) ))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition magic_items_safety_wit_35 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) <= 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (1 <= k)) (PreH8 : (k <= c_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH12 : (c_pre <= (ListLib.sum (al)))) (PreH13 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH14 : (0 <= ans)) (PreH15 : (ans <= 10000000)) (PreH16 : (Forall (Z.le (1)) al )) (PreH17 : (Forall2 Z.le al bl )) (PreH18 : (Forall (Z.ge (10000)) bl )) (PreH19 : (Forall (Z.le (0)) dl )) (PreH20 : (Forall (Z.ge (10000001)) dl )) (PreH21 : forall (q: Z) , (((0 <= q) /\ (q <= k)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition magic_items_safety_wit_36 := 
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH11 : (c_pre <= (ListLib.sum (al)))) (PreH12 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH13 : (0 <= ans)) (PreH14 : (ans <= 10000000)) (PreH15 : (Forall (Z.le (1)) al )) (PreH16 : (Forall2 Z.le al bl )) (PreH17 : (Forall (Z.ge (10000)) bl )) (PreH18 : (Forall (Z.le (0)) dl )) (PreH19 : (Forall (Z.ge (10000001)) dl )) (PreH20 : forall (q: Z) , (((0 <= q) /\ (q <= k)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) ,
  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ ((ans - (Znth k dl 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ans - (Znth k dl 0) )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH11 : (c_pre <= (ListLib.sum (al)))) (PreH12 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH13 : (0 <= ans)) (PreH14 : (ans <= 10000000)) (PreH15 : (Forall (Z.le (1)) al )) (PreH16 : (Forall2 Z.le al bl )) (PreH17 : (Forall (Z.ge (10000)) bl )) (PreH18 : (Forall (Z.le (0)) dl )) (PreH19 : (Forall (Z.ge (10000001)) dl )) (PreH20 : forall (q: Z) , (((0 <= q) /\ (q <= k)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) ,
  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ ((ans - (Znth k dl 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ans - (Znth k dl 0) )) ”
).

Definition magic_items_safety_wit_36_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH11 : (c_pre <= (ListLib.sum (al)))) (PreH12 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH13 : (0 <= ans)) (PreH14 : (ans <= 10000000)) (PreH15 : (Forall (Z.le (1)) al )) (PreH16 : (Forall2 Z.le al bl )) (PreH17 : (Forall (Z.ge (10000)) bl )) (PreH18 : (Forall (Z.le (0)) dl )) (PreH19 : (Forall (Z.ge (10000001)) dl )) (PreH20 : forall (q: Z) , (((0 <= q) /\ (q <= k)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) ,
  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ ((ans - (Znth k dl 0) ) <= INT_MAX) ”
.

Definition magic_items_safety_wit_36_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH11 : (c_pre <= (ListLib.sum (al)))) (PreH12 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH13 : (0 <= ans)) (PreH14 : (ans <= 10000000)) (PreH15 : (Forall (Z.le (1)) al )) (PreH16 : (Forall2 Z.le al bl )) (PreH17 : (Forall (Z.ge (10000)) bl )) (PreH18 : (Forall (Z.le (0)) dl )) (PreH19 : (Forall (Z.ge (10000001)) dl )) (PreH20 : forall (q: Z) , (((0 <= q) /\ (q <= k)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) ,
  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ ((INT_MIN) <= (ans - (Znth k dl 0) )) ”
.

Definition magic_items_entail_wit_1 := 
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (1 <= c_pre)) (PreH4 : (c_pre <= 5000)) (PreH5 : (Forall (Z.le (1)) al )) (PreH6 : (Forall2 Z.le al bl )) (PreH7 : (Forall (Z.ge (10000)) bl )) ,
  (IntArray.undef_full ( &( "dp" ) ) 5001 )
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 5000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (Forall (Z.le (1)) al ) ” 
  &&  “ (Forall2 Z.le al bl ) ” 
  &&  “ (Forall (Z.ge (10000)) bl ) ” 
  &&  “ (0 = (ListLib.sum ((sublist (0) (0) (al))))) ” 
  &&  “ (0 = (FreeCash (c_pre) ((sublist (0) (0) (al))) ((sublist (0) (0) (bl))))) ” 
  &&  “ (0 = (UnconstrainedRevenue (c_pre) ((sublist (0) (0) (al))) ((sublist (0) (0) (bl))))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (10000 * 0 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (10000 * 0 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (10000 * 0 )) ”
  &&  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
) \/
(
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (1 <= c_pre)) (PreH4 : (c_pre <= 5000)) (PreH5 : (Forall (Z.le (1)) al )) (PreH6 : (Forall2 Z.le al bl )) (PreH7 : (Forall (Z.ge (10000)) bl )) ,
  TT && emp 
|--
  “ (0 = (UnconstrainedRevenue (c_pre) ((sublist (0) (0) (al))) ((sublist (0) (0) (bl))))) ” 
  &&  “ (0 = (FreeCash (c_pre) ((sublist (0) (0) (al))) ((sublist (0) (0) (bl))))) ” 
  &&  “ (0 = (ListLib.sum ((sublist (0) (0) (al))))) ”
  &&  emp
).

Definition magic_items_entail_wit_1_split_goal_1 := 
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (1 <= c_pre)) (PreH4 : (c_pre <= 5000)) (PreH5 : (Forall (Z.le (1)) al )) (PreH6 : (Forall2 Z.le al bl )) (PreH7 : (Forall (Z.ge (10000)) bl )) ,
  (0 = (UnconstrainedRevenue (c_pre) ((sublist (0) (0) (al))) ((sublist (0) (0) (bl)))))
.

Definition magic_items_entail_wit_1_split_goal_2 := 
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (1 <= c_pre)) (PreH4 : (c_pre <= 5000)) (PreH5 : (Forall (Z.le (1)) al )) (PreH6 : (Forall2 Z.le al bl )) (PreH7 : (Forall (Z.ge (10000)) bl )) ,
  (0 = (FreeCash (c_pre) ((sublist (0) (0) (al))) ((sublist (0) (0) (bl)))))
.

Definition magic_items_entail_wit_1_split_goal_3 := 
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (1 <= c_pre)) (PreH4 : (c_pre <= 5000)) (PreH5 : (Forall (Z.le (1)) al )) (PreH6 : (Forall2 Z.le al bl )) (PreH7 : (Forall (Z.ge (10000)) bl )) ,
  (0 = (ListLib.sum ((sublist (0) (0) (al)))))
.

Definition magic_items_entail_wit_2_1 := 
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) > 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall (Z.le (1)) al )) (PreH10 : (Forall2 Z.le al bl )) (PreH11 : (Forall (Z.ge (10000)) bl )) (PreH12 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH13 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (0 <= t)) (PreH16 : (t <= (10000 * i ))) (PreH17 : (0 <= s)) (PreH18 : (s <= (10000 * i ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 5000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (Forall (Z.le (1)) al ) ” 
  &&  “ (Forall2 Z.le al bl ) ” 
  &&  “ (Forall (Z.ge (10000)) bl ) ” 
  &&  “ ((t + (Znth i al 0) ) = (ListLib.sum ((sublist (0) ((i + 1 )) (al))))) ” 
  &&  “ (s = (FreeCash (c_pre) ((sublist (0) ((i + 1 )) (al))) ((sublist (0) ((i + 1 )) (bl))))) ” 
  &&  “ (((ans + (Znth i al 0) ) + (((Znth i bl 0) - (Znth i al 0) ) - c_pre ) ) = (UnconstrainedRevenue (c_pre) ((sublist (0) ((i + 1 )) (al))) ((sublist (0) ((i + 1 )) (bl))))) ” 
  &&  “ (0 <= (t + (Znth i al 0) )) ” 
  &&  “ ((t + (Znth i al 0) ) <= (10000 * (i + 1 ) )) ” 
  &&  “ (0 <= s) ” 
  &&  “ (s <= (10000 * (i + 1 ) )) ” 
  &&  “ (0 <= ((ans + (Znth i al 0) ) + (((Znth i bl 0) - (Znth i al 0) ) - c_pre ) )) ” 
  &&  “ (((ans + (Znth i al 0) ) + (((Znth i bl 0) - (Znth i al 0) ) - c_pre ) ) <= (10000 * (i + 1 ) )) ”
  &&  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
) \/
(
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) > 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall (Z.le (1)) al )) (PreH10 : (Forall2 Z.le al bl )) (PreH11 : (Forall (Z.ge (10000)) bl )) (PreH12 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH13 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (0 <= t)) (PreH16 : (t <= (10000 * i ))) (PreH17 : (0 <= s)) (PreH18 : (s <= (10000 * i ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= (10000 * i ))) ,
  TT && emp 
|--
  “ (((ans + (Znth i al 0) ) + (((Znth i bl 0) - (Znth i al 0) ) - c_pre ) ) <= (10000 * (i + 1 ) )) ” 
  &&  “ (0 <= ((ans + (Znth i al 0) ) + (((Znth i bl 0) - (Znth i al 0) ) - c_pre ) )) ” 
  &&  “ ((t + (Znth i al 0) ) <= (10000 * (i + 1 ) )) ” 
  &&  “ (0 <= (t + (Znth i al 0) )) ” 
  &&  “ (((ans + (Znth i al 0) ) + (((Znth i bl 0) - (Znth i al 0) ) - c_pre ) ) = (UnconstrainedRevenue (c_pre) ((sublist (0) ((i + 1 )) (al))) ((sublist (0) ((i + 1 )) (bl))))) ” 
  &&  “ (s = (FreeCash (c_pre) ((sublist (0) ((i + 1 )) (al))) ((sublist (0) ((i + 1 )) (bl))))) ” 
  &&  “ ((t + (Znth i al 0) ) = (ListLib.sum ((sublist (0) ((i + 1 )) (al))))) ”
  &&  emp
).

Definition magic_items_entail_wit_2_1_split_goal_1 := 
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) > 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall (Z.le (1)) al )) (PreH10 : (Forall2 Z.le al bl )) (PreH11 : (Forall (Z.ge (10000)) bl )) (PreH12 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH13 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (0 <= t)) (PreH16 : (t <= (10000 * i ))) (PreH17 : (0 <= s)) (PreH18 : (s <= (10000 * i ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= (10000 * i ))) ,
  (((ans + (Znth i al 0) ) + (((Znth i bl 0) - (Znth i al 0) ) - c_pre ) ) <= (10000 * (i + 1 ) ))
.

Definition magic_items_entail_wit_2_1_split_goal_2 := 
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) > 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall (Z.le (1)) al )) (PreH10 : (Forall2 Z.le al bl )) (PreH11 : (Forall (Z.ge (10000)) bl )) (PreH12 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH13 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (0 <= t)) (PreH16 : (t <= (10000 * i ))) (PreH17 : (0 <= s)) (PreH18 : (s <= (10000 * i ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= (10000 * i ))) ,
  (0 <= ((ans + (Znth i al 0) ) + (((Znth i bl 0) - (Znth i al 0) ) - c_pre ) ))
.

Definition magic_items_entail_wit_2_1_split_goal_3 := 
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) > 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall (Z.le (1)) al )) (PreH10 : (Forall2 Z.le al bl )) (PreH11 : (Forall (Z.ge (10000)) bl )) (PreH12 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH13 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (0 <= t)) (PreH16 : (t <= (10000 * i ))) (PreH17 : (0 <= s)) (PreH18 : (s <= (10000 * i ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= (10000 * i ))) ,
  ((t + (Znth i al 0) ) <= (10000 * (i + 1 ) ))
.

Definition magic_items_entail_wit_2_1_split_goal_4 := 
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) > 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall (Z.le (1)) al )) (PreH10 : (Forall2 Z.le al bl )) (PreH11 : (Forall (Z.ge (10000)) bl )) (PreH12 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH13 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (0 <= t)) (PreH16 : (t <= (10000 * i ))) (PreH17 : (0 <= s)) (PreH18 : (s <= (10000 * i ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= (10000 * i ))) ,
  (0 <= (t + (Znth i al 0) ))
.

Definition magic_items_entail_wit_2_1_split_goal_5 := 
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) > 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall (Z.le (1)) al )) (PreH10 : (Forall2 Z.le al bl )) (PreH11 : (Forall (Z.ge (10000)) bl )) (PreH12 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH13 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (0 <= t)) (PreH16 : (t <= (10000 * i ))) (PreH17 : (0 <= s)) (PreH18 : (s <= (10000 * i ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= (10000 * i ))) ,
  (((ans + (Znth i al 0) ) + (((Znth i bl 0) - (Znth i al 0) ) - c_pre ) ) = (UnconstrainedRevenue (c_pre) ((sublist (0) ((i + 1 )) (al))) ((sublist (0) ((i + 1 )) (bl)))))
.

Definition magic_items_entail_wit_2_1_split_goal_6 := 
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) > 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall (Z.le (1)) al )) (PreH10 : (Forall2 Z.le al bl )) (PreH11 : (Forall (Z.ge (10000)) bl )) (PreH12 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH13 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (0 <= t)) (PreH16 : (t <= (10000 * i ))) (PreH17 : (0 <= s)) (PreH18 : (s <= (10000 * i ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= (10000 * i ))) ,
  (s = (FreeCash (c_pre) ((sublist (0) ((i + 1 )) (al))) ((sublist (0) ((i + 1 )) (bl)))))
.

Definition magic_items_entail_wit_2_1_split_goal_7 := 
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) > 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall (Z.le (1)) al )) (PreH10 : (Forall2 Z.le al bl )) (PreH11 : (Forall (Z.ge (10000)) bl )) (PreH12 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH13 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (0 <= t)) (PreH16 : (t <= (10000 * i ))) (PreH17 : (0 <= s)) (PreH18 : (s <= (10000 * i ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= (10000 * i ))) ,
  ((t + (Znth i al 0) ) = (ListLib.sum ((sublist (0) ((i + 1 )) (al)))))
.

Definition magic_items_entail_wit_2_2 := 
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) <= 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall (Z.le (1)) al )) (PreH10 : (Forall2 Z.le al bl )) (PreH11 : (Forall (Z.ge (10000)) bl )) (PreH12 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH13 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (0 <= t)) (PreH16 : (t <= (10000 * i ))) (PreH17 : (0 <= s)) (PreH18 : (s <= (10000 * i ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 5000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (Forall (Z.le (1)) al ) ” 
  &&  “ (Forall2 Z.le al bl ) ” 
  &&  “ (Forall (Z.ge (10000)) bl ) ” 
  &&  “ ((t + (Znth i al 0) ) = (ListLib.sum ((sublist (0) ((i + 1 )) (al))))) ” 
  &&  “ ((s + (Znth i al 0) ) = (FreeCash (c_pre) ((sublist (0) ((i + 1 )) (al))) ((sublist (0) ((i + 1 )) (bl))))) ” 
  &&  “ ((ans + (Znth i al 0) ) = (UnconstrainedRevenue (c_pre) ((sublist (0) ((i + 1 )) (al))) ((sublist (0) ((i + 1 )) (bl))))) ” 
  &&  “ (0 <= (t + (Znth i al 0) )) ” 
  &&  “ ((t + (Znth i al 0) ) <= (10000 * (i + 1 ) )) ” 
  &&  “ (0 <= (s + (Znth i al 0) )) ” 
  &&  “ ((s + (Znth i al 0) ) <= (10000 * (i + 1 ) )) ” 
  &&  “ (0 <= (ans + (Znth i al 0) )) ” 
  &&  “ ((ans + (Znth i al 0) ) <= (10000 * (i + 1 ) )) ”
  &&  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
) \/
(
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) <= 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall (Z.le (1)) al )) (PreH10 : (Forall2 Z.le al bl )) (PreH11 : (Forall (Z.ge (10000)) bl )) (PreH12 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH13 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (0 <= t)) (PreH16 : (t <= (10000 * i ))) (PreH17 : (0 <= s)) (PreH18 : (s <= (10000 * i ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= (10000 * i ))) ,
  TT && emp 
|--
  “ ((ans + (Znth i al 0) ) <= (10000 * (i + 1 ) )) ” 
  &&  “ (0 <= (ans + (Znth i al 0) )) ” 
  &&  “ ((s + (Znth i al 0) ) <= (10000 * (i + 1 ) )) ” 
  &&  “ (0 <= (s + (Znth i al 0) )) ” 
  &&  “ ((t + (Znth i al 0) ) <= (10000 * (i + 1 ) )) ” 
  &&  “ (0 <= (t + (Znth i al 0) )) ” 
  &&  “ ((ans + (Znth i al 0) ) = (UnconstrainedRevenue (c_pre) ((sublist (0) ((i + 1 )) (al))) ((sublist (0) ((i + 1 )) (bl))))) ” 
  &&  “ ((s + (Znth i al 0) ) = (FreeCash (c_pre) ((sublist (0) ((i + 1 )) (al))) ((sublist (0) ((i + 1 )) (bl))))) ” 
  &&  “ ((t + (Znth i al 0) ) = (ListLib.sum ((sublist (0) ((i + 1 )) (al))))) ”
  &&  emp
).

Definition magic_items_entail_wit_2_2_split_goal_1 := 
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) <= 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall (Z.le (1)) al )) (PreH10 : (Forall2 Z.le al bl )) (PreH11 : (Forall (Z.ge (10000)) bl )) (PreH12 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH13 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (0 <= t)) (PreH16 : (t <= (10000 * i ))) (PreH17 : (0 <= s)) (PreH18 : (s <= (10000 * i ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= (10000 * i ))) ,
  ((ans + (Znth i al 0) ) <= (10000 * (i + 1 ) ))
.

Definition magic_items_entail_wit_2_2_split_goal_2 := 
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) <= 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall (Z.le (1)) al )) (PreH10 : (Forall2 Z.le al bl )) (PreH11 : (Forall (Z.ge (10000)) bl )) (PreH12 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH13 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (0 <= t)) (PreH16 : (t <= (10000 * i ))) (PreH17 : (0 <= s)) (PreH18 : (s <= (10000 * i ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= (10000 * i ))) ,
  (0 <= (ans + (Znth i al 0) ))
.

Definition magic_items_entail_wit_2_2_split_goal_3 := 
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) <= 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall (Z.le (1)) al )) (PreH10 : (Forall2 Z.le al bl )) (PreH11 : (Forall (Z.ge (10000)) bl )) (PreH12 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH13 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (0 <= t)) (PreH16 : (t <= (10000 * i ))) (PreH17 : (0 <= s)) (PreH18 : (s <= (10000 * i ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= (10000 * i ))) ,
  ((s + (Znth i al 0) ) <= (10000 * (i + 1 ) ))
.

Definition magic_items_entail_wit_2_2_split_goal_4 := 
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) <= 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall (Z.le (1)) al )) (PreH10 : (Forall2 Z.le al bl )) (PreH11 : (Forall (Z.ge (10000)) bl )) (PreH12 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH13 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (0 <= t)) (PreH16 : (t <= (10000 * i ))) (PreH17 : (0 <= s)) (PreH18 : (s <= (10000 * i ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= (10000 * i ))) ,
  (0 <= (s + (Znth i al 0) ))
.

Definition magic_items_entail_wit_2_2_split_goal_5 := 
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) <= 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall (Z.le (1)) al )) (PreH10 : (Forall2 Z.le al bl )) (PreH11 : (Forall (Z.ge (10000)) bl )) (PreH12 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH13 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (0 <= t)) (PreH16 : (t <= (10000 * i ))) (PreH17 : (0 <= s)) (PreH18 : (s <= (10000 * i ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= (10000 * i ))) ,
  ((t + (Znth i al 0) ) <= (10000 * (i + 1 ) ))
.

Definition magic_items_entail_wit_2_2_split_goal_6 := 
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) <= 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall (Z.le (1)) al )) (PreH10 : (Forall2 Z.le al bl )) (PreH11 : (Forall (Z.ge (10000)) bl )) (PreH12 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH13 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (0 <= t)) (PreH16 : (t <= (10000 * i ))) (PreH17 : (0 <= s)) (PreH18 : (s <= (10000 * i ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= (10000 * i ))) ,
  (0 <= (t + (Znth i al 0) ))
.

Definition magic_items_entail_wit_2_2_split_goal_7 := 
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) <= 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall (Z.le (1)) al )) (PreH10 : (Forall2 Z.le al bl )) (PreH11 : (Forall (Z.ge (10000)) bl )) (PreH12 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH13 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (0 <= t)) (PreH16 : (t <= (10000 * i ))) (PreH17 : (0 <= s)) (PreH18 : (s <= (10000 * i ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= (10000 * i ))) ,
  ((ans + (Znth i al 0) ) = (UnconstrainedRevenue (c_pre) ((sublist (0) ((i + 1 )) (al))) ((sublist (0) ((i + 1 )) (bl)))))
.

Definition magic_items_entail_wit_2_2_split_goal_8 := 
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) <= 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall (Z.le (1)) al )) (PreH10 : (Forall2 Z.le al bl )) (PreH11 : (Forall (Z.ge (10000)) bl )) (PreH12 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH13 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (0 <= t)) (PreH16 : (t <= (10000 * i ))) (PreH17 : (0 <= s)) (PreH18 : (s <= (10000 * i ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= (10000 * i ))) ,
  ((s + (Znth i al 0) ) = (FreeCash (c_pre) ((sublist (0) ((i + 1 )) (al))) ((sublist (0) ((i + 1 )) (bl)))))
.

Definition magic_items_entail_wit_2_2_split_goal_9 := 
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) <= 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall (Z.le (1)) al )) (PreH10 : (Forall2 Z.le al bl )) (PreH11 : (Forall (Z.ge (10000)) bl )) (PreH12 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH13 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (0 <= t)) (PreH16 : (t <= (10000 * i ))) (PreH17 : (0 <= s)) (PreH18 : (s <= (10000 * i ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= (10000 * i ))) ,
  ((t + (Znth i al 0) ) = (ListLib.sum ((sublist (0) ((i + 1 )) (al)))))
.

Definition magic_items_entail_wit_3 := 
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : (s < c_pre)) (PreH2 : (t >= c_pre)) (PreH3 : (i >= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 5000)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (Forall (Z.le (1)) al )) (PreH11 : (Forall2 Z.le al bl )) (PreH12 : (Forall (Z.ge (10000)) bl )) (PreH13 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH14 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH16 : (0 <= t)) (PreH17 : (t <= (10000 * i ))) (PreH18 : (0 <= s)) (PreH19 : (s <= (10000 * i ))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= (10000 * i ))) ,
  (((( &( "dp" ) ) + (0 * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.undef_seg ( &( "dp" ) ) 1 5001 )
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
|--
  EX (dl: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 5000) ” 
  &&  “ (1 <= (c_pre - s )) ” 
  &&  “ ((c_pre - s ) <= c_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= ((c_pre - s ) + 1 )) ” 
  &&  “ ((c_pre - s ) = (c_pre - (FreeCash (c_pre) (al) (bl)) )) ” 
  &&  “ (c_pre <= (ListLib.sum (al))) ” 
  &&  “ (ans = (UnconstrainedRevenue (c_pre) (al) (bl))) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= 10000000) ” 
  &&  “ (Forall (Z.le (1)) al ) ” 
  &&  “ (Forall2 Z.le al bl ) ” 
  &&  “ (Forall (Z.ge (10000)) bl ) ” 
  &&  “ ((Znth (0) (dl) (0)) = 0) ” 
  &&  “ (Forall (eq (10000001)) (sublist (1) (1) (dl)) ) ”
  &&  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |->_)
  **  (IntArray.seg ( &( "dp" ) ) 0 1 dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) 1 5001 )
) \/
(
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : (0 <= INT_MAX)) (PreH2 : (0 >= INT_MIN)) (PreH3 : (s < c_pre)) (PreH4 : (t >= c_pre)) (PreH5 : (i >= n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : (1 <= c_pre)) (PreH9 : (c_pre <= 5000)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall (Z.le (1)) al )) (PreH13 : (Forall2 Z.le al bl )) (PreH14 : (Forall (Z.ge (10000)) bl )) (PreH15 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH16 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH17 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH18 : (0 <= t)) (PreH19 : (t <= (10000 * i ))) (PreH20 : (0 <= s)) (PreH21 : (s <= (10000 * i ))) (PreH22 : (0 <= ans)) (PreH23 : (ans <= (10000 * i ))) ,
  (((( &( "dp" ) ) + (0 * sizeof(INT)))) # Int  |-> 0)
|--
  EX (dl: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 5000) ” 
  &&  “ (1 <= (c_pre - s )) ” 
  &&  “ ((c_pre - s ) <= c_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= ((c_pre - s ) + 1 )) ” 
  &&  “ ((c_pre - s ) = (c_pre - (FreeCash (c_pre) (al) (bl)) )) ” 
  &&  “ (c_pre <= (ListLib.sum (al))) ” 
  &&  “ (ans = (UnconstrainedRevenue (c_pre) (al) (bl))) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= 10000000) ” 
  &&  “ (Forall (Z.le (1)) al ) ” 
  &&  “ (Forall2 Z.le al bl ) ” 
  &&  “ (Forall (Z.ge (10000)) bl ) ” 
  &&  “ ((Znth (0) (dl) (0)) = 0) ” 
  &&  “ (Forall (eq (10000001)) (sublist (1) (1) (dl)) ) ”
  &&  (IntArray.seg ( &( "dp" ) ) 0 1 dl )
).

Definition magic_items_entail_wit_4 := 
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl_2: (@list Z)) (ans: Z) (j: Z) (k: Z) (PreH1 : (j <= k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= (k + 1 ))) (PreH10 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH11 : (c_pre <= (ListLib.sum (al)))) (PreH12 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH13 : (0 <= ans)) (PreH14 : (ans <= 10000000)) (PreH15 : (Forall (Z.le (1)) al )) (PreH16 : (Forall2 Z.le al bl )) (PreH17 : (Forall (Z.ge (10000)) bl )) (PreH18 : ((Znth (0) (dl_2) (0)) = 0)) (PreH19 : (Forall (eq (10000001)) (sublist (1) (j) (dl_2)) )) ,
  (IntArray.seg ( &( "dp" ) ) 0 (j + 1 ) (app (dl_2) ((cons (10000001) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "dp" ) ) (j + 1 ) 5001 )
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
|--
  EX (dl: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 5000) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= c_pre) ” 
  &&  “ (1 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (k + 1 )) ” 
  &&  “ (k = (c_pre - (FreeCash (c_pre) (al) (bl)) )) ” 
  &&  “ (c_pre <= (ListLib.sum (al))) ” 
  &&  “ (ans = (UnconstrainedRevenue (c_pre) (al) (bl))) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= 10000000) ” 
  &&  “ (Forall (Z.le (1)) al ) ” 
  &&  “ (Forall2 Z.le al bl ) ” 
  &&  “ (Forall (Z.ge (10000)) bl ) ” 
  &&  “ ((Znth (0) (dl) (0)) = 0) ” 
  &&  “ (Forall (eq (10000001)) (sublist (1) ((j + 1 )) (dl)) ) ”
  &&  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.seg ( &( "dp" ) ) 0 (j + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (j + 1 ) 5001 )
) \/
(
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl_2: (@list Z)) (ans: Z) (j: Z) (k: Z) (PreH1 : (j <= k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= (k + 1 ))) (PreH10 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH11 : (c_pre <= (ListLib.sum (al)))) (PreH12 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH13 : (0 <= ans)) (PreH14 : (ans <= 10000000)) (PreH15 : (Forall (Z.le (1)) al )) (PreH16 : (Forall2 Z.le al bl )) (PreH17 : (Forall (Z.ge (10000)) bl )) (PreH18 : ((Znth (0) (dl_2) (0)) = 0)) (PreH19 : (Forall (eq (10000001)) (sublist (1) (j) (dl_2)) )) ,
  TT && emp 
|--
  “ (Forall (eq (10000001)) (sublist (1) ((j + 1 )) ((app (dl_2) ((cons (10000001) ((@nil Z))))))) ) ” 
  &&  “ ((Znth (0) ((app (dl_2) ((cons (10000001) ((@nil Z)))))) (0)) = 0) ”
  &&  emp
).

Definition magic_items_entail_wit_4_split_goal_1 := 
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl_2: (@list Z)) (ans: Z) (j: Z) (k: Z) (PreH1 : (j <= k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= (k + 1 ))) (PreH10 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH11 : (c_pre <= (ListLib.sum (al)))) (PreH12 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH13 : (0 <= ans)) (PreH14 : (ans <= 10000000)) (PreH15 : (Forall (Z.le (1)) al )) (PreH16 : (Forall2 Z.le al bl )) (PreH17 : (Forall (Z.ge (10000)) bl )) (PreH18 : ((Znth (0) (dl_2) (0)) = 0)) (PreH19 : (Forall (eq (10000001)) (sublist (1) (j) (dl_2)) )) ,
  (Forall (eq (10000001)) (sublist (1) ((j + 1 )) ((app (dl_2) ((cons (10000001) ((@nil Z))))))) )
.

Definition magic_items_entail_wit_4_split_goal_2 := 
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl_2: (@list Z)) (ans: Z) (j: Z) (k: Z) (PreH1 : (j <= k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= (k + 1 ))) (PreH10 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH11 : (c_pre <= (ListLib.sum (al)))) (PreH12 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH13 : (0 <= ans)) (PreH14 : (ans <= 10000000)) (PreH15 : (Forall (Z.le (1)) al )) (PreH16 : (Forall2 Z.le al bl )) (PreH17 : (Forall (Z.ge (10000)) bl )) (PreH18 : ((Znth (0) (dl_2) (0)) = 0)) (PreH19 : (Forall (eq (10000001)) (sublist (1) (j) (dl_2)) )) ,
  ((Znth (0) ((app (dl_2) ((cons (10000001) ((@nil Z)))))) (0)) = 0)
.

Definition magic_items_entail_wit_5 := 
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl_2: (@list Z)) (ans: Z) (j: Z) (k: Z) (PreH1 : (j > k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= (k + 1 ))) (PreH10 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH11 : (c_pre <= (ListLib.sum (al)))) (PreH12 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH13 : (0 <= ans)) (PreH14 : (ans <= 10000000)) (PreH15 : (Forall (Z.le (1)) al )) (PreH16 : (Forall2 Z.le al bl )) (PreH17 : (Forall (Z.ge (10000)) bl )) (PreH18 : ((Znth (0) (dl_2) (0)) = 0)) (PreH19 : (Forall (eq (10000001)) (sublist (1) (j) (dl_2)) )) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.seg ( &( "dp" ) ) 0 j dl_2 )
  **  (IntArray.undef_seg ( &( "dp" ) ) j 5001 )
|--
  EX (dl: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 5000) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= c_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (k = (c_pre - (FreeCash (c_pre) (al) (bl)) )) ” 
  &&  “ (c_pre <= (ListLib.sum (al))) ” 
  &&  “ (ans = (UnconstrainedRevenue (c_pre) (al) (bl))) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= 10000000) ” 
  &&  “ (Forall (Z.le (1)) al ) ” 
  &&  “ (Forall2 Z.le al bl ) ” 
  &&  “ (Forall (Z.ge (10000)) bl ) ” 
  &&  “ (Forall (Z.le (0)) dl ) ” 
  &&  “ (Forall (Z.ge (10000001)) dl ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= k)) -> (MinimumSacrifice c_pre al bl 0 q (Znth (q) (dl) (0)) )) ”
  &&  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
) \/
(
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl_2: (@list Z)) (ans: Z) (j: Z) (k: Z) (PreH1 : (j > k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= (k + 1 ))) (PreH10 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH11 : (c_pre <= (ListLib.sum (al)))) (PreH12 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH13 : (0 <= ans)) (PreH14 : (ans <= 10000000)) (PreH15 : (Forall (Z.le (1)) al )) (PreH16 : (Forall2 Z.le al bl )) (PreH17 : (Forall (Z.ge (10000)) bl )) (PreH18 : ((Znth (0) (dl_2) (0)) = 0)) (PreH19 : (Forall (eq (10000001)) (sublist (1) (j) (dl_2)) )) ,
  (IntArray.seg ( &( "dp" ) ) 0 j dl_2 )
|--
  EX (dl: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 5000) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= c_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (k = (c_pre - (FreeCash (c_pre) (al) (bl)) )) ” 
  &&  “ (c_pre <= (ListLib.sum (al))) ” 
  &&  “ (ans = (UnconstrainedRevenue (c_pre) (al) (bl))) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= 10000000) ” 
  &&  “ (Forall (Z.le (1)) al ) ” 
  &&  “ (Forall2 Z.le al bl ) ” 
  &&  “ (Forall (Z.ge (10000)) bl ) ” 
  &&  “ (Forall (Z.le (0)) dl ) ” 
  &&  “ (Forall (Z.ge (10000001)) dl ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= k)) -> (MinimumSacrifice c_pre al bl 0 q (Znth (q) (dl) (0)) )) ”
  &&  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
).

Definition magic_items_entail_wit_6 := 
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl_2: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) > 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (1 <= k)) (PreH8 : (k <= c_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH12 : (c_pre <= (ListLib.sum (al)))) (PreH13 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH14 : (0 <= ans)) (PreH15 : (ans <= 10000000)) (PreH16 : (Forall (Z.le (1)) al )) (PreH17 : (Forall2 Z.le al bl )) (PreH18 : (Forall (Z.ge (10000)) bl )) (PreH19 : (Forall (Z.le (0)) dl_2 )) (PreH20 : (Forall (Z.ge (10000001)) dl_2 )) (PreH21 : forall (q_3: Z) , (((0 <= q_3) /\ (q_3 <= k)) -> (MinimumSacrifice c_pre al bl i q_3 (Znth (q_3) (dl_2) (0)) ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl_2 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  EX (dl: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 5000) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= c_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= k) ” 
  &&  “ (1 <= (Znth i al 0)) ” 
  &&  “ ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre )) ” 
  &&  “ (0 < (((Znth i bl 0) - (Znth i al 0) ) - c_pre )) ” 
  &&  “ (k = (c_pre - (FreeCash (c_pre) (al) (bl)) )) ” 
  &&  “ (c_pre <= (ListLib.sum (al))) ” 
  &&  “ (ans = (UnconstrainedRevenue (c_pre) (al) (bl))) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= 10000000) ” 
  &&  “ (Forall (Z.le (1)) al ) ” 
  &&  “ (Forall2 Z.le al bl ) ” 
  &&  “ (Forall (Z.ge (10000)) bl ) ” 
  &&  “ (Forall (Z.le (0)) dl ) ” 
  &&  “ (Forall (Z.ge (10000001)) dl ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= k)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) )) ” 
  &&  “ forall (q_2: Z) , (((k < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) )) ”
  &&  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
) \/
(
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl_2: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) > 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (1 <= k)) (PreH8 : (k <= c_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH12 : (c_pre <= (ListLib.sum (al)))) (PreH13 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH14 : (0 <= ans)) (PreH15 : (ans <= 10000000)) (PreH16 : (Forall (Z.le (1)) al )) (PreH17 : (Forall2 Z.le al bl )) (PreH18 : (Forall (Z.ge (10000)) bl )) (PreH19 : (Forall (Z.le (0)) dl_2 )) (PreH20 : (Forall (Z.ge (10000001)) dl_2 )) (PreH21 : forall (q_3: Z) , (((0 <= q_3) /\ (q_3 <= k)) -> (MinimumSacrifice c_pre al bl i q_3 (Znth (q_3) (dl_2) (0)) ))) ,
  TT && emp 
|--
  “ forall (q_2: Z) , (((k < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl_2) (0)) )) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= k)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl_2) (0)) )) ” 
  &&  “ (1 <= (Znth i al 0)) ”
  &&  emp
).

Definition magic_items_entail_wit_6_split_goal_1 := 
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl_2: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) > 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (1 <= k)) (PreH8 : (k <= c_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH12 : (c_pre <= (ListLib.sum (al)))) (PreH13 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH14 : (0 <= ans)) (PreH15 : (ans <= 10000000)) (PreH16 : (Forall (Z.le (1)) al )) (PreH17 : (Forall2 Z.le al bl )) (PreH18 : (Forall (Z.ge (10000)) bl )) (PreH19 : (Forall (Z.le (0)) dl_2 )) (PreH20 : (Forall (Z.ge (10000001)) dl_2 )) (PreH21 : forall (q_3: Z) , (((0 <= q_3) /\ (q_3 <= k)) -> (MinimumSacrifice c_pre al bl i q_3 (Znth (q_3) (dl_2) (0)) ))) ,
  forall (q_2: Z) , (((k < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl_2) (0)) ))
.

Definition magic_items_entail_wit_6_split_goal_2 := 
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl_2: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) > 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (1 <= k)) (PreH8 : (k <= c_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH12 : (c_pre <= (ListLib.sum (al)))) (PreH13 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH14 : (0 <= ans)) (PreH15 : (ans <= 10000000)) (PreH16 : (Forall (Z.le (1)) al )) (PreH17 : (Forall2 Z.le al bl )) (PreH18 : (Forall (Z.ge (10000)) bl )) (PreH19 : (Forall (Z.le (0)) dl_2 )) (PreH20 : (Forall (Z.ge (10000001)) dl_2 )) (PreH21 : forall (q_3: Z) , (((0 <= q_3) /\ (q_3 <= k)) -> (MinimumSacrifice c_pre al bl i q_3 (Znth (q_3) (dl_2) (0)) ))) ,
  forall (q: Z) , (((0 <= q) /\ (q <= k)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl_2) (0)) ))
.

Definition magic_items_entail_wit_6_split_goal_3 := 
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl_2: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) > 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (1 <= k)) (PreH8 : (k <= c_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH12 : (c_pre <= (ListLib.sum (al)))) (PreH13 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH14 : (0 <= ans)) (PreH15 : (ans <= 10000000)) (PreH16 : (Forall (Z.le (1)) al )) (PreH17 : (Forall2 Z.le al bl )) (PreH18 : (Forall (Z.ge (10000)) bl )) (PreH19 : (Forall (Z.le (0)) dl_2 )) (PreH20 : (Forall (Z.ge (10000001)) dl_2 )) (PreH21 : forall (q_3: Z) , (((0 <= q_3) /\ (q_3 <= k)) -> (MinimumSacrifice c_pre al bl i q_3 (Znth (q_3) (dl_2) (0)) ))) ,
  (1 <= (Znth i al 0))
.

Definition magic_items_entail_wit_7_1 := 
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl_2: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (((Znth 0 dl_2 0) + d ) < (Znth j dl_2 0))) (PreH2 : ((j - (Znth i al 0) ) < 0)) (PreH3 : (j > 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 5000)) (PreH8 : (1 <= k)) (PreH9 : (k <= c_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= k)) (PreH14 : (1 <= (Znth i al 0))) (PreH15 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH16 : (0 < d)) (PreH17 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH18 : (c_pre <= (ListLib.sum (al)))) (PreH19 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= 10000000)) (PreH22 : (Forall (Z.le (1)) al )) (PreH23 : (Forall2 Z.le al bl )) (PreH24 : (Forall (Z.ge (10000)) bl )) (PreH25 : (Forall (Z.le (0)) dl_2 )) (PreH26 : (Forall (Z.ge (10000001)) dl_2 )) (PreH27 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl_2) (0)) ))) (PreH28 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl_2) (0)) ))) ,
  (IntArray.full ( &( "dp" ) ) (k + 1 ) (replace_Znth (j) (((Znth 0 dl_2 0) + d )) (dl_2)) )
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  EX (dl: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 5000) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= c_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (j - 1 )) ” 
  &&  “ ((j - 1 ) <= k) ” 
  &&  “ (1 <= (Znth i al 0)) ” 
  &&  “ (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre )) ” 
  &&  “ (0 < d) ” 
  &&  “ (k = (c_pre - (FreeCash (c_pre) (al) (bl)) )) ” 
  &&  “ (c_pre <= (ListLib.sum (al))) ” 
  &&  “ (ans = (UnconstrainedRevenue (c_pre) (al) (bl))) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= 10000000) ” 
  &&  “ (Forall (Z.le (1)) al ) ” 
  &&  “ (Forall2 Z.le al bl ) ” 
  &&  “ (Forall (Z.ge (10000)) bl ) ” 
  &&  “ (Forall (Z.le (0)) dl ) ” 
  &&  “ (Forall (Z.ge (10000001)) dl ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= (j - 1 ))) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) )) ” 
  &&  “ forall (q_2: Z) , ((((j - 1 ) < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) )) ”
  &&  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
) \/
(
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl_2: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (((Znth 0 dl_2 0) + d ) < (Znth j dl_2 0))) (PreH2 : ((j - (Znth i al 0) ) < 0)) (PreH3 : (j > 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 5000)) (PreH8 : (1 <= k)) (PreH9 : (k <= c_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= k)) (PreH14 : (1 <= (Znth i al 0))) (PreH15 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH16 : (0 < d)) (PreH17 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH18 : (c_pre <= (ListLib.sum (al)))) (PreH19 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= 10000000)) (PreH22 : (Forall (Z.le (1)) al )) (PreH23 : (Forall2 Z.le al bl )) (PreH24 : (Forall (Z.ge (10000)) bl )) (PreH25 : (Forall (Z.le (0)) dl_2 )) (PreH26 : (Forall (Z.ge (10000001)) dl_2 )) (PreH27 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl_2) (0)) ))) (PreH28 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl_2) (0)) ))) ,
  TT && emp 
|--
  “ (Forall (Z.ge (10000001)) (replace_Znth (j) (((Znth 0 dl_2 0) + d )) (dl_2)) ) ” 
  &&  “ (Forall (Z.le (0)) (replace_Znth (j) (((Znth 0 dl_2 0) + d )) (dl_2)) ) ”
  &&  emp
).

Definition magic_items_entail_wit_7_1_split_goal_1 := 
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl_2: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (((Znth 0 dl_2 0) + d ) < (Znth j dl_2 0))) (PreH2 : ((j - (Znth i al 0) ) < 0)) (PreH3 : (j > 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 5000)) (PreH8 : (1 <= k)) (PreH9 : (k <= c_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= k)) (PreH14 : (1 <= (Znth i al 0))) (PreH15 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH16 : (0 < d)) (PreH17 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH18 : (c_pre <= (ListLib.sum (al)))) (PreH19 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= 10000000)) (PreH22 : (Forall (Z.le (1)) al )) (PreH23 : (Forall2 Z.le al bl )) (PreH24 : (Forall (Z.ge (10000)) bl )) (PreH25 : (Forall (Z.le (0)) dl_2 )) (PreH26 : (Forall (Z.ge (10000001)) dl_2 )) (PreH27 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl_2) (0)) ))) (PreH28 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl_2) (0)) ))) ,
  (Forall (Z.ge (10000001)) (replace_Znth (j) (((Znth 0 dl_2 0) + d )) (dl_2)) )
.

Definition magic_items_entail_wit_7_1_split_goal_2 := 
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl_2: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (((Znth 0 dl_2 0) + d ) < (Znth j dl_2 0))) (PreH2 : ((j - (Znth i al 0) ) < 0)) (PreH3 : (j > 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 5000)) (PreH8 : (1 <= k)) (PreH9 : (k <= c_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= k)) (PreH14 : (1 <= (Znth i al 0))) (PreH15 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH16 : (0 < d)) (PreH17 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH18 : (c_pre <= (ListLib.sum (al)))) (PreH19 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= 10000000)) (PreH22 : (Forall (Z.le (1)) al )) (PreH23 : (Forall2 Z.le al bl )) (PreH24 : (Forall (Z.ge (10000)) bl )) (PreH25 : (Forall (Z.le (0)) dl_2 )) (PreH26 : (Forall (Z.ge (10000001)) dl_2 )) (PreH27 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl_2) (0)) ))) (PreH28 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl_2) (0)) ))) ,
  (Forall (Z.le (0)) (replace_Znth (j) (((Znth 0 dl_2 0) + d )) (dl_2)) )
.

Definition magic_items_entail_wit_7_2 := 
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl_2: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (((Znth (j - (Znth i al 0) ) dl_2 0) + d ) < (Znth j dl_2 0))) (PreH2 : ((j - (Znth i al 0) ) >= 0)) (PreH3 : (j > 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 5000)) (PreH8 : (1 <= k)) (PreH9 : (k <= c_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= k)) (PreH14 : (1 <= (Znth i al 0))) (PreH15 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH16 : (0 < d)) (PreH17 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH18 : (c_pre <= (ListLib.sum (al)))) (PreH19 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= 10000000)) (PreH22 : (Forall (Z.le (1)) al )) (PreH23 : (Forall2 Z.le al bl )) (PreH24 : (Forall (Z.ge (10000)) bl )) (PreH25 : (Forall (Z.le (0)) dl_2 )) (PreH26 : (Forall (Z.ge (10000001)) dl_2 )) (PreH27 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl_2) (0)) ))) (PreH28 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl_2) (0)) ))) ,
  (IntArray.full ( &( "dp" ) ) (k + 1 ) (replace_Znth (j) (((Znth (j - (Znth i al 0) ) dl_2 0) + d )) (dl_2)) )
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  EX (dl: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 5000) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= c_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (j - 1 )) ” 
  &&  “ ((j - 1 ) <= k) ” 
  &&  “ (1 <= (Znth i al 0)) ” 
  &&  “ (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre )) ” 
  &&  “ (0 < d) ” 
  &&  “ (k = (c_pre - (FreeCash (c_pre) (al) (bl)) )) ” 
  &&  “ (c_pre <= (ListLib.sum (al))) ” 
  &&  “ (ans = (UnconstrainedRevenue (c_pre) (al) (bl))) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= 10000000) ” 
  &&  “ (Forall (Z.le (1)) al ) ” 
  &&  “ (Forall2 Z.le al bl ) ” 
  &&  “ (Forall (Z.ge (10000)) bl ) ” 
  &&  “ (Forall (Z.le (0)) dl ) ” 
  &&  “ (Forall (Z.ge (10000001)) dl ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= (j - 1 ))) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) )) ” 
  &&  “ forall (q_2: Z) , ((((j - 1 ) < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) )) ”
  &&  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
) \/
(
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl_2: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (((Znth (j - (Znth i al 0) ) dl_2 0) + d ) < (Znth j dl_2 0))) (PreH2 : ((j - (Znth i al 0) ) >= 0)) (PreH3 : (j > 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 5000)) (PreH8 : (1 <= k)) (PreH9 : (k <= c_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= k)) (PreH14 : (1 <= (Znth i al 0))) (PreH15 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH16 : (0 < d)) (PreH17 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH18 : (c_pre <= (ListLib.sum (al)))) (PreH19 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= 10000000)) (PreH22 : (Forall (Z.le (1)) al )) (PreH23 : (Forall2 Z.le al bl )) (PreH24 : (Forall (Z.ge (10000)) bl )) (PreH25 : (Forall (Z.le (0)) dl_2 )) (PreH26 : (Forall (Z.ge (10000001)) dl_2 )) (PreH27 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl_2) (0)) ))) (PreH28 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl_2) (0)) ))) ,
  TT && emp 
|--
  “ (Forall (Z.ge (10000001)) (replace_Znth (j) (((Znth (j - (Znth i al 0) ) dl_2 0) + d )) (dl_2)) ) ” 
  &&  “ (Forall (Z.le (0)) (replace_Znth (j) (((Znth (j - (Znth i al 0) ) dl_2 0) + d )) (dl_2)) ) ”
  &&  emp
).

Definition magic_items_entail_wit_7_2_split_goal_1 := 
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl_2: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (((Znth (j - (Znth i al 0) ) dl_2 0) + d ) < (Znth j dl_2 0))) (PreH2 : ((j - (Znth i al 0) ) >= 0)) (PreH3 : (j > 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 5000)) (PreH8 : (1 <= k)) (PreH9 : (k <= c_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= k)) (PreH14 : (1 <= (Znth i al 0))) (PreH15 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH16 : (0 < d)) (PreH17 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH18 : (c_pre <= (ListLib.sum (al)))) (PreH19 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= 10000000)) (PreH22 : (Forall (Z.le (1)) al )) (PreH23 : (Forall2 Z.le al bl )) (PreH24 : (Forall (Z.ge (10000)) bl )) (PreH25 : (Forall (Z.le (0)) dl_2 )) (PreH26 : (Forall (Z.ge (10000001)) dl_2 )) (PreH27 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl_2) (0)) ))) (PreH28 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl_2) (0)) ))) ,
  (Forall (Z.ge (10000001)) (replace_Znth (j) (((Znth (j - (Znth i al 0) ) dl_2 0) + d )) (dl_2)) )
.

Definition magic_items_entail_wit_7_2_split_goal_2 := 
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl_2: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (((Znth (j - (Znth i al 0) ) dl_2 0) + d ) < (Znth j dl_2 0))) (PreH2 : ((j - (Znth i al 0) ) >= 0)) (PreH3 : (j > 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 5000)) (PreH8 : (1 <= k)) (PreH9 : (k <= c_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= k)) (PreH14 : (1 <= (Znth i al 0))) (PreH15 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH16 : (0 < d)) (PreH17 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH18 : (c_pre <= (ListLib.sum (al)))) (PreH19 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= 10000000)) (PreH22 : (Forall (Z.le (1)) al )) (PreH23 : (Forall2 Z.le al bl )) (PreH24 : (Forall (Z.ge (10000)) bl )) (PreH25 : (Forall (Z.le (0)) dl_2 )) (PreH26 : (Forall (Z.ge (10000001)) dl_2 )) (PreH27 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl_2) (0)) ))) (PreH28 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl_2) (0)) ))) ,
  (Forall (Z.le (0)) (replace_Znth (j) (((Znth (j - (Znth i al 0) ) dl_2 0) + d )) (dl_2)) )
.

Definition magic_items_entail_wit_7_3 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl_2: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (((Znth 0 dl_2 0) + d ) >= (Znth j dl_2 0))) (PreH2 : ((j - (Znth i al 0) ) < 0)) (PreH3 : (j > 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 5000)) (PreH8 : (1 <= k)) (PreH9 : (k <= c_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= k)) (PreH14 : (1 <= (Znth i al 0))) (PreH15 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH16 : (0 < d)) (PreH17 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH18 : (c_pre <= (ListLib.sum (al)))) (PreH19 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= 10000000)) (PreH22 : (Forall (Z.le (1)) al )) (PreH23 : (Forall2 Z.le al bl )) (PreH24 : (Forall (Z.ge (10000)) bl )) (PreH25 : (Forall (Z.le (0)) dl_2 )) (PreH26 : (Forall (Z.ge (10000001)) dl_2 )) (PreH27 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl_2) (0)) ))) (PreH28 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl_2) (0)) ))) ,
  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl_2 )
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  EX (dl: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 5000) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= c_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (j - 1 )) ” 
  &&  “ ((j - 1 ) <= k) ” 
  &&  “ (1 <= (Znth i al 0)) ” 
  &&  “ (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre )) ” 
  &&  “ (0 < d) ” 
  &&  “ (k = (c_pre - (FreeCash (c_pre) (al) (bl)) )) ” 
  &&  “ (c_pre <= (ListLib.sum (al))) ” 
  &&  “ (ans = (UnconstrainedRevenue (c_pre) (al) (bl))) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= 10000000) ” 
  &&  “ (Forall (Z.le (1)) al ) ” 
  &&  “ (Forall2 Z.le al bl ) ” 
  &&  “ (Forall (Z.ge (10000)) bl ) ” 
  &&  “ (Forall (Z.le (0)) dl ) ” 
  &&  “ (Forall (Z.ge (10000001)) dl ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= (j - 1 ))) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) )) ” 
  &&  “ forall (q_2: Z) , ((((j - 1 ) < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) )) ”
  &&  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
.

Definition magic_items_entail_wit_7_4 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl_2: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (((Znth (j - (Znth i al 0) ) dl_2 0) + d ) >= (Znth j dl_2 0))) (PreH2 : ((j - (Znth i al 0) ) >= 0)) (PreH3 : (j > 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 5000)) (PreH8 : (1 <= k)) (PreH9 : (k <= c_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= k)) (PreH14 : (1 <= (Znth i al 0))) (PreH15 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH16 : (0 < d)) (PreH17 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH18 : (c_pre <= (ListLib.sum (al)))) (PreH19 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= 10000000)) (PreH22 : (Forall (Z.le (1)) al )) (PreH23 : (Forall2 Z.le al bl )) (PreH24 : (Forall (Z.ge (10000)) bl )) (PreH25 : (Forall (Z.le (0)) dl_2 )) (PreH26 : (Forall (Z.ge (10000001)) dl_2 )) (PreH27 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl_2) (0)) ))) (PreH28 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl_2) (0)) ))) ,
  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl_2 )
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  EX (dl: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 5000) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= c_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (j - 1 )) ” 
  &&  “ ((j - 1 ) <= k) ” 
  &&  “ (1 <= (Znth i al 0)) ” 
  &&  “ (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre )) ” 
  &&  “ (0 < d) ” 
  &&  “ (k = (c_pre - (FreeCash (c_pre) (al) (bl)) )) ” 
  &&  “ (c_pre <= (ListLib.sum (al))) ” 
  &&  “ (ans = (UnconstrainedRevenue (c_pre) (al) (bl))) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= 10000000) ” 
  &&  “ (Forall (Z.le (1)) al ) ” 
  &&  “ (Forall2 Z.le al bl ) ” 
  &&  “ (Forall (Z.ge (10000)) bl ) ” 
  &&  “ (Forall (Z.le (0)) dl ) ” 
  &&  “ (Forall (Z.ge (10000001)) dl ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= (j - 1 ))) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) )) ” 
  &&  “ forall (q_2: Z) , ((((j - 1 ) < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) )) ”
  &&  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
.

Definition magic_items_entail_wit_8_1 := 
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl_2: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (j <= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= k)) (PreH12 : (1 <= (Znth i al 0))) (PreH13 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH14 : (0 < d)) (PreH15 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH16 : (c_pre <= (ListLib.sum (al)))) (PreH17 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= 10000000)) (PreH20 : (Forall (Z.le (1)) al )) (PreH21 : (Forall2 Z.le al bl )) (PreH22 : (Forall (Z.ge (10000)) bl )) (PreH23 : (Forall (Z.le (0)) dl_2 )) (PreH24 : (Forall (Z.ge (10000001)) dl_2 )) (PreH25 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 <= j)) -> (MinimumSacrifice c_pre al bl i q_2 (Znth (q_2) (dl_2) (0)) ))) (PreH26 : forall (q_3: Z) , (((j < q_3) /\ (q_3 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_3 (Znth (q_3) (dl_2) (0)) ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl_2 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  EX (dl: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 5000) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= c_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (k = (c_pre - (FreeCash (c_pre) (al) (bl)) )) ” 
  &&  “ (c_pre <= (ListLib.sum (al))) ” 
  &&  “ (ans = (UnconstrainedRevenue (c_pre) (al) (bl))) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= 10000000) ” 
  &&  “ (Forall (Z.le (1)) al ) ” 
  &&  “ (Forall2 Z.le al bl ) ” 
  &&  “ (Forall (Z.ge (10000)) bl ) ” 
  &&  “ (Forall (Z.le (0)) dl ) ” 
  &&  “ (Forall (Z.ge (10000001)) dl ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q (Znth (q) (dl) (0)) )) ”
  &&  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
) \/
(
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl_2: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (j <= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= k)) (PreH12 : (1 <= (Znth i al 0))) (PreH13 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH14 : (0 < d)) (PreH15 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH16 : (c_pre <= (ListLib.sum (al)))) (PreH17 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= 10000000)) (PreH20 : (Forall (Z.le (1)) al )) (PreH21 : (Forall2 Z.le al bl )) (PreH22 : (Forall (Z.ge (10000)) bl )) (PreH23 : (Forall (Z.le (0)) dl_2 )) (PreH24 : (Forall (Z.ge (10000001)) dl_2 )) (PreH25 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 <= j)) -> (MinimumSacrifice c_pre al bl i q_2 (Znth (q_2) (dl_2) (0)) ))) (PreH26 : forall (q_3: Z) , (((j < q_3) /\ (q_3 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_3 (Znth (q_3) (dl_2) (0)) ))) ,
  TT && emp 
|--
  “ forall (q: Z) , (((0 <= q) /\ (q <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q (Znth (q) (dl_2) (0)) )) ”
  &&  emp
).

Definition magic_items_entail_wit_8_1_split_goal_1 := 
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl_2: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (j <= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= k)) (PreH12 : (1 <= (Znth i al 0))) (PreH13 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH14 : (0 < d)) (PreH15 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH16 : (c_pre <= (ListLib.sum (al)))) (PreH17 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= 10000000)) (PreH20 : (Forall (Z.le (1)) al )) (PreH21 : (Forall2 Z.le al bl )) (PreH22 : (Forall (Z.ge (10000)) bl )) (PreH23 : (Forall (Z.le (0)) dl_2 )) (PreH24 : (Forall (Z.ge (10000001)) dl_2 )) (PreH25 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 <= j)) -> (MinimumSacrifice c_pre al bl i q_2 (Znth (q_2) (dl_2) (0)) ))) (PreH26 : forall (q_3: Z) , (((j < q_3) /\ (q_3 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_3 (Znth (q_3) (dl_2) (0)) ))) ,
  forall (q: Z) , (((0 <= q) /\ (q <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q (Znth (q) (dl_2) (0)) ))
.

Definition magic_items_entail_wit_8_2 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl_2: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) <= 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (1 <= k)) (PreH8 : (k <= c_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH12 : (c_pre <= (ListLib.sum (al)))) (PreH13 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH14 : (0 <= ans)) (PreH15 : (ans <= 10000000)) (PreH16 : (Forall (Z.le (1)) al )) (PreH17 : (Forall2 Z.le al bl )) (PreH18 : (Forall (Z.ge (10000)) bl )) (PreH19 : (Forall (Z.le (0)) dl_2 )) (PreH20 : (Forall (Z.ge (10000001)) dl_2 )) (PreH21 : forall (q: Z) , (((0 <= q) /\ (q <= k)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl_2) (0)) ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl_2 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  EX (dl: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 5000) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= c_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (k = (c_pre - (FreeCash (c_pre) (al) (bl)) )) ” 
  &&  “ (c_pre <= (ListLib.sum (al))) ” 
  &&  “ (ans = (UnconstrainedRevenue (c_pre) (al) (bl))) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= 10000000) ” 
  &&  “ (Forall (Z.le (1)) al ) ” 
  &&  “ (Forall2 Z.le al bl ) ” 
  &&  “ (Forall (Z.ge (10000)) bl ) ” 
  &&  “ (Forall (Z.le (0)) dl ) ” 
  &&  “ (Forall (Z.ge (10000001)) dl ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q (Znth (q) (dl) (0)) )) ”
  &&  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
.

Definition magic_items_entail_wit_9 := 
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH11 : (c_pre <= (ListLib.sum (al)))) (PreH12 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH13 : (0 <= ans)) (PreH14 : (ans <= 10000000)) (PreH15 : (Forall (Z.le (1)) al )) (PreH16 : (Forall2 Z.le al bl )) (PreH17 : (Forall (Z.ge (10000)) bl )) (PreH18 : (Forall (Z.le (0)) dl )) (PreH19 : (Forall (Z.ge (10000001)) dl )) (PreH20 : forall (q: Z) , (((0 <= q) /\ (q <= k)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) ,
  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ (MaximumMagicRevenue c_pre al bl (ans - (Znth k dl 0) ) ) ”
  &&  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
  **  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |->_)
) \/
(
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH11 : (c_pre <= (ListLib.sum (al)))) (PreH12 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH13 : (0 <= ans)) (PreH14 : (ans <= 10000000)) (PreH15 : (Forall (Z.le (1)) al )) (PreH16 : (Forall2 Z.le al bl )) (PreH17 : (Forall (Z.ge (10000)) bl )) (PreH18 : (Forall (Z.le (0)) dl )) (PreH19 : (Forall (Z.ge (10000001)) dl )) (PreH20 : forall (q: Z) , (((0 <= q) /\ (q <= k)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) ,
  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ (MaximumMagicRevenue c_pre al bl (ans - (Znth k dl 0) ) ) ”
  &&  (IntArray.undef_full ( &( "dp" ) ) 5001 )
).

Definition magic_items_entail_wit_9_split_goal_1 := 
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH11 : (c_pre <= (ListLib.sum (al)))) (PreH12 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH13 : (0 <= ans)) (PreH14 : (ans <= 10000000)) (PreH15 : (Forall (Z.le (1)) al )) (PreH16 : (Forall2 Z.le al bl )) (PreH17 : (Forall (Z.ge (10000)) bl )) (PreH18 : (Forall (Z.le (0)) dl )) (PreH19 : (Forall (Z.ge (10000001)) dl )) (PreH20 : forall (q: Z) , (((0 <= q) /\ (q <= k)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) ,
  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ (MaximumMagicRevenue c_pre al bl (ans - (Znth k dl 0) ) ) ”
.

Definition magic_items_entail_wit_9_split_goal_spatial := 
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH11 : (c_pre <= (ListLib.sum (al)))) (PreH12 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH13 : (0 <= ans)) (PreH14 : (ans <= 10000000)) (PreH15 : (Forall (Z.le (1)) al )) (PreH16 : (Forall2 Z.le al bl )) (PreH17 : (Forall (Z.ge (10000)) bl )) (PreH18 : (Forall (Z.le (0)) dl )) (PreH19 : (Forall (Z.ge (10000001)) dl )) (PreH20 : forall (q: Z) , (((0 <= q) /\ (q <= k)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) ,
  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  (IntArray.undef_full ( &( "dp" ) ) 5001 )
.

Definition magic_items_return_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (result: Z) (PreH1 : (MaximumMagicRevenue c_pre al bl result )) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
|--
  “ (MaximumMagicRevenue c_pre al bl result ) ”
  &&  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
.

Definition magic_items_return_wit_2 := 
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : (s >= c_pre)) (PreH2 : (t >= c_pre)) (PreH3 : (i >= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 5000)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (Forall (Z.le (1)) al )) (PreH11 : (Forall2 Z.le al bl )) (PreH12 : (Forall (Z.ge (10000)) bl )) (PreH13 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH14 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH16 : (0 <= t)) (PreH17 : (t <= (10000 * i ))) (PreH18 : (0 <= s)) (PreH19 : (s <= (10000 * i ))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
|--
  “ (MaximumMagicRevenue c_pre al bl ans ) ”
  &&  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
) \/
(
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : (s >= c_pre)) (PreH2 : (t >= c_pre)) (PreH3 : (i >= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 5000)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (Forall (Z.le (1)) al )) (PreH11 : (Forall2 Z.le al bl )) (PreH12 : (Forall (Z.ge (10000)) bl )) (PreH13 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH14 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH16 : (0 <= t)) (PreH17 : (t <= (10000 * i ))) (PreH18 : (0 <= s)) (PreH19 : (s <= (10000 * i ))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= (10000 * i ))) ,
  TT && emp 
|--
  “ (MaximumMagicRevenue c_pre al bl ans ) ”
  &&  emp
).

Definition magic_items_return_wit_2_split_goal_1 := 
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : (s >= c_pre)) (PreH2 : (t >= c_pre)) (PreH3 : (i >= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 5000)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (Forall (Z.le (1)) al )) (PreH11 : (Forall2 Z.le al bl )) (PreH12 : (Forall (Z.ge (10000)) bl )) (PreH13 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH14 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH16 : (0 <= t)) (PreH17 : (t <= (10000 * i ))) (PreH18 : (0 <= s)) (PreH19 : (s <= (10000 * i ))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= (10000 * i ))) ,
  (MaximumMagicRevenue c_pre al bl ans )
.

Definition magic_items_return_wit_3 := 
(
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : (t < c_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall (Z.le (1)) al )) (PreH10 : (Forall2 Z.le al bl )) (PreH11 : (Forall (Z.ge (10000)) bl )) (PreH12 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH13 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (0 <= t)) (PreH16 : (t <= (10000 * i ))) (PreH17 : (0 <= s)) (PreH18 : (s <= (10000 * i ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
|--
  “ (MaximumMagicRevenue c_pre al bl t ) ”
  &&  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
) \/
(
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : (t < c_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall (Z.le (1)) al )) (PreH10 : (Forall2 Z.le al bl )) (PreH11 : (Forall (Z.ge (10000)) bl )) (PreH12 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH13 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (0 <= t)) (PreH16 : (t <= (10000 * i ))) (PreH17 : (0 <= s)) (PreH18 : (s <= (10000 * i ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= (10000 * i ))) ,
  TT && emp 
|--
  “ (MaximumMagicRevenue c_pre al bl t ) ”
  &&  emp
).

Definition magic_items_return_wit_3_split_goal_1 := 
forall (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : (t < c_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall (Z.le (1)) al )) (PreH10 : (Forall2 Z.le al bl )) (PreH11 : (Forall (Z.ge (10000)) bl )) (PreH12 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH13 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (0 <= t)) (PreH16 : (t <= (10000 * i ))) (PreH17 : (0 <= s)) (PreH18 : (s <= (10000 * i ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= (10000 * i ))) ,
  (MaximumMagicRevenue c_pre al bl t )
.

Definition magic_items_partial_solve_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (Forall (Z.le (1)) al )) (PreH9 : (Forall2 Z.le al bl )) (PreH10 : (Forall (Z.ge (10000)) bl )) (PreH11 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH12 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH13 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (0 <= t)) (PreH15 : (t <= (10000 * i ))) (PreH16 : (0 <= s)) (PreH17 : (s <= (10000 * i ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 5000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (Forall (Z.le (1)) al ) ” 
  &&  “ (Forall2 Z.le al bl ) ” 
  &&  “ (Forall (Z.ge (10000)) bl ) ” 
  &&  “ (t = (ListLib.sum ((sublist (0) (i) (al))))) ” 
  &&  “ (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl))))) ” 
  &&  “ (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl))))) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= (10000 * i )) ” 
  &&  “ (0 <= s) ” 
  &&  “ (s <= (10000 * i )) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= (10000 * i )) ”
  &&  (((b_pre + (i * sizeof(INT)))) # Int  |-> (Znth i bl 0))
  **  (IntArray.missing_i b_pre i 0 n_pre bl )
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
.

Definition magic_items_partial_solve_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (Forall (Z.le (1)) al )) (PreH9 : (Forall2 Z.le al bl )) (PreH10 : (Forall (Z.ge (10000)) bl )) (PreH11 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH12 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH13 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (0 <= t)) (PreH15 : (t <= (10000 * i ))) (PreH16 : (0 <= s)) (PreH17 : (s <= (10000 * i ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= (10000 * i ))) ,
  (IntArray.full b_pre n_pre bl )
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 5000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (Forall (Z.le (1)) al ) ” 
  &&  “ (Forall2 Z.le al bl ) ” 
  &&  “ (Forall (Z.ge (10000)) bl ) ” 
  &&  “ (t = (ListLib.sum ((sublist (0) (i) (al))))) ” 
  &&  “ (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl))))) ” 
  &&  “ (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl))))) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= (10000 * i )) ” 
  &&  “ (0 <= s) ” 
  &&  “ (s <= (10000 * i )) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= (10000 * i )) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i al 0))
  **  (IntArray.missing_i a_pre i 0 n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
.

Definition magic_items_partial_solve_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (Forall (Z.le (1)) al )) (PreH9 : (Forall2 Z.le al bl )) (PreH10 : (Forall (Z.ge (10000)) bl )) (PreH11 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH12 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH13 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (0 <= t)) (PreH15 : (t <= (10000 * i ))) (PreH16 : (0 <= s)) (PreH17 : (s <= (10000 * i ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 5000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (Forall (Z.le (1)) al ) ” 
  &&  “ (Forall2 Z.le al bl ) ” 
  &&  “ (Forall (Z.ge (10000)) bl ) ” 
  &&  “ (t = (ListLib.sum ((sublist (0) (i) (al))))) ” 
  &&  “ (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl))))) ” 
  &&  “ (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl))))) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= (10000 * i )) ” 
  &&  “ (0 <= s) ” 
  &&  “ (s <= (10000 * i )) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= (10000 * i )) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i al 0))
  **  (IntArray.missing_i a_pre i 0 n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
.

Definition magic_items_partial_solve_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (Forall (Z.le (1)) al )) (PreH9 : (Forall2 Z.le al bl )) (PreH10 : (Forall (Z.ge (10000)) bl )) (PreH11 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH12 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH13 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (0 <= t)) (PreH15 : (t <= (10000 * i ))) (PreH16 : (0 <= s)) (PreH17 : (s <= (10000 * i ))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 5000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (Forall (Z.le (1)) al ) ” 
  &&  “ (Forall2 Z.le al bl ) ” 
  &&  “ (Forall (Z.ge (10000)) bl ) ” 
  &&  “ (t = (ListLib.sum ((sublist (0) (i) (al))))) ” 
  &&  “ (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl))))) ” 
  &&  “ (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl))))) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= (10000 * i )) ” 
  &&  “ (0 <= s) ” 
  &&  “ (s <= (10000 * i )) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= (10000 * i )) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i al 0))
  **  (IntArray.missing_i a_pre i 0 n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
.

Definition magic_items_partial_solve_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) <= 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (Forall (Z.le (1)) al )) (PreH10 : (Forall2 Z.le al bl )) (PreH11 : (Forall (Z.ge (10000)) bl )) (PreH12 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH13 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH14 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (0 <= t)) (PreH16 : (t <= (10000 * i ))) (PreH17 : (0 <= s)) (PreH18 : (s <= (10000 * i ))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ ((((Znth i bl 0) - (Znth i al 0) ) - c_pre ) <= 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 5000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (Forall (Z.le (1)) al ) ” 
  &&  “ (Forall2 Z.le al bl ) ” 
  &&  “ (Forall (Z.ge (10000)) bl ) ” 
  &&  “ (t = (ListLib.sum ((sublist (0) (i) (al))))) ” 
  &&  “ (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl))))) ” 
  &&  “ (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl))))) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= (10000 * i )) ” 
  &&  “ (0 <= s) ” 
  &&  “ (s <= (10000 * i )) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= (10000 * i )) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i al 0))
  **  (IntArray.missing_i a_pre i 0 n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
.

Definition magic_items_partial_solve_wit_6 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (ans: Z) (s: Z) (t: Z) (i: Z) (PreH1 : (s < c_pre)) (PreH2 : (t >= c_pre)) (PreH3 : (i >= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 5000)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (Forall (Z.le (1)) al )) (PreH11 : (Forall2 Z.le al bl )) (PreH12 : (Forall (Z.ge (10000)) bl )) (PreH13 : (t = (ListLib.sum ((sublist (0) (i) (al)))))) (PreH14 : (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH15 : (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl)))))) (PreH16 : (0 <= t)) (PreH17 : (t <= (10000 * i ))) (PreH18 : (0 <= s)) (PreH19 : (s <= (10000 * i ))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= (10000 * i ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.undef_full ( &( "dp" ) ) 5001 )
|--
  “ (s < c_pre) ” 
  &&  “ (t >= c_pre) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 5000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (Forall (Z.le (1)) al ) ” 
  &&  “ (Forall2 Z.le al bl ) ” 
  &&  “ (Forall (Z.ge (10000)) bl ) ” 
  &&  “ (t = (ListLib.sum ((sublist (0) (i) (al))))) ” 
  &&  “ (s = (FreeCash (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl))))) ” 
  &&  “ (ans = (UnconstrainedRevenue (c_pre) ((sublist (0) (i) (al))) ((sublist (0) (i) (bl))))) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= (10000 * i )) ” 
  &&  “ (0 <= s) ” 
  &&  “ (s <= (10000 * i )) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= (10000 * i )) ”
  &&  (((( &( "dp" ) ) + (0 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "dp" ) ) 1 5001 )
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
.

Definition magic_items_partial_solve_wit_7 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (j: Z) (k: Z) (PreH1 : (j <= k)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= (k + 1 ))) (PreH10 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH11 : (c_pre <= (ListLib.sum (al)))) (PreH12 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH13 : (0 <= ans)) (PreH14 : (ans <= 10000000)) (PreH15 : (Forall (Z.le (1)) al )) (PreH16 : (Forall2 Z.le al bl )) (PreH17 : (Forall (Z.ge (10000)) bl )) (PreH18 : ((Znth (0) (dl) (0)) = 0)) (PreH19 : (Forall (eq (10000001)) (sublist (1) (j) (dl)) )) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.seg ( &( "dp" ) ) 0 j dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) j 5001 )
|--
  “ (j <= k) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 5000) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= c_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= (k + 1 )) ” 
  &&  “ (k = (c_pre - (FreeCash (c_pre) (al) (bl)) )) ” 
  &&  “ (c_pre <= (ListLib.sum (al))) ” 
  &&  “ (ans = (UnconstrainedRevenue (c_pre) (al) (bl))) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= 10000000) ” 
  &&  “ (Forall (Z.le (1)) al ) ” 
  &&  “ (Forall2 Z.le al bl ) ” 
  &&  “ (Forall (Z.ge (10000)) bl ) ” 
  &&  “ ((Znth (0) (dl) (0)) = 0) ” 
  &&  “ (Forall (eq (10000001)) (sublist (1) (j) (dl)) ) ”
  &&  (((( &( "dp" ) ) + (j * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "dp" ) ) (j + 1 ) 5001 )
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.seg ( &( "dp" ) ) 0 j dl )
.

Definition magic_items_partial_solve_wit_8 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH11 : (c_pre <= (ListLib.sum (al)))) (PreH12 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH13 : (0 <= ans)) (PreH14 : (ans <= 10000000)) (PreH15 : (Forall (Z.le (1)) al )) (PreH16 : (Forall2 Z.le al bl )) (PreH17 : (Forall (Z.ge (10000)) bl )) (PreH18 : (Forall (Z.le (0)) dl )) (PreH19 : (Forall (Z.ge (10000001)) dl )) (PreH20 : forall (q: Z) , (((0 <= q) /\ (q <= k)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 5000) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= c_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (k = (c_pre - (FreeCash (c_pre) (al) (bl)) )) ” 
  &&  “ (c_pre <= (ListLib.sum (al))) ” 
  &&  “ (ans = (UnconstrainedRevenue (c_pre) (al) (bl))) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= 10000000) ” 
  &&  “ (Forall (Z.le (1)) al ) ” 
  &&  “ (Forall2 Z.le al bl ) ” 
  &&  “ (Forall (Z.ge (10000)) bl ) ” 
  &&  “ (Forall (Z.le (0)) dl ) ” 
  &&  “ (Forall (Z.ge (10000001)) dl ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= k)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) )) ”
  &&  (((b_pre + (i * sizeof(INT)))) # Int  |-> (Znth i bl 0))
  **  (IntArray.missing_i b_pre i 0 n_pre bl )
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
.

Definition magic_items_partial_solve_wit_9 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH11 : (c_pre <= (ListLib.sum (al)))) (PreH12 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH13 : (0 <= ans)) (PreH14 : (ans <= 10000000)) (PreH15 : (Forall (Z.le (1)) al )) (PreH16 : (Forall2 Z.le al bl )) (PreH17 : (Forall (Z.ge (10000)) bl )) (PreH18 : (Forall (Z.le (0)) dl )) (PreH19 : (Forall (Z.ge (10000001)) dl )) (PreH20 : forall (q: Z) , (((0 <= q) /\ (q <= k)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) ,
  (IntArray.full b_pre n_pre bl )
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 5000) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= c_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (k = (c_pre - (FreeCash (c_pre) (al) (bl)) )) ” 
  &&  “ (c_pre <= (ListLib.sum (al))) ” 
  &&  “ (ans = (UnconstrainedRevenue (c_pre) (al) (bl))) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= 10000000) ” 
  &&  “ (Forall (Z.le (1)) al ) ” 
  &&  “ (Forall2 Z.le al bl ) ” 
  &&  “ (Forall (Z.ge (10000)) bl ) ” 
  &&  “ (Forall (Z.le (0)) dl ) ” 
  &&  “ (Forall (Z.ge (10000001)) dl ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= k)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) )) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i al 0))
  **  (IntArray.missing_i a_pre i 0 n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
.

Definition magic_items_partial_solve_wit_10 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (j > 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j <= k)) (PreH12 : (1 <= (Znth i al 0))) (PreH13 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH14 : (0 < d)) (PreH15 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH16 : (c_pre <= (ListLib.sum (al)))) (PreH17 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH18 : (0 <= ans)) (PreH19 : (ans <= 10000000)) (PreH20 : (Forall (Z.le (1)) al )) (PreH21 : (Forall2 Z.le al bl )) (PreH22 : (Forall (Z.ge (10000)) bl )) (PreH23 : (Forall (Z.le (0)) dl )) (PreH24 : (Forall (Z.ge (10000001)) dl )) (PreH25 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) (PreH26 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ (j > 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 5000) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= c_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= k) ” 
  &&  “ (1 <= (Znth i al 0)) ” 
  &&  “ (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre )) ” 
  &&  “ (0 < d) ” 
  &&  “ (k = (c_pre - (FreeCash (c_pre) (al) (bl)) )) ” 
  &&  “ (c_pre <= (ListLib.sum (al))) ” 
  &&  “ (ans = (UnconstrainedRevenue (c_pre) (al) (bl))) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= 10000000) ” 
  &&  “ (Forall (Z.le (1)) al ) ” 
  &&  “ (Forall2 Z.le al bl ) ” 
  &&  “ (Forall (Z.ge (10000)) bl ) ” 
  &&  “ (Forall (Z.le (0)) dl ) ” 
  &&  “ (Forall (Z.ge (10000001)) dl ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) )) ” 
  &&  “ forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) )) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i al 0))
  **  (IntArray.missing_i a_pre i 0 n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
.

Definition magic_items_partial_solve_wit_11 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : ((j - (Znth i al 0) ) < 0)) (PreH2 : (j > 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (1 <= k)) (PreH8 : (k <= c_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= k)) (PreH13 : (1 <= (Znth i al 0))) (PreH14 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH15 : (0 < d)) (PreH16 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH17 : (c_pre <= (ListLib.sum (al)))) (PreH18 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= 10000000)) (PreH21 : (Forall (Z.le (1)) al )) (PreH22 : (Forall2 Z.le al bl )) (PreH23 : (Forall (Z.ge (10000)) bl )) (PreH24 : (Forall (Z.le (0)) dl )) (PreH25 : (Forall (Z.ge (10000001)) dl )) (PreH26 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) (PreH27 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ ((j - (Znth i al 0) ) < 0) ” 
  &&  “ (j > 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 5000) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= c_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= k) ” 
  &&  “ (1 <= (Znth i al 0)) ” 
  &&  “ (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre )) ” 
  &&  “ (0 < d) ” 
  &&  “ (k = (c_pre - (FreeCash (c_pre) (al) (bl)) )) ” 
  &&  “ (c_pre <= (ListLib.sum (al))) ” 
  &&  “ (ans = (UnconstrainedRevenue (c_pre) (al) (bl))) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= 10000000) ” 
  &&  “ (Forall (Z.le (1)) al ) ” 
  &&  “ (Forall2 Z.le al bl ) ” 
  &&  “ (Forall (Z.ge (10000)) bl ) ” 
  &&  “ (Forall (Z.le (0)) dl ) ” 
  &&  “ (Forall (Z.ge (10000001)) dl ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) )) ” 
  &&  “ forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) )) ”
  &&  (((( &( "dp" ) ) + (0 * sizeof(INT)))) # Int  |-> (Znth 0 dl 0))
  **  (IntArray.missing_i ( &( "dp" ) ) 0 0 (k + 1 ) dl )
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
.

Definition magic_items_partial_solve_wit_12 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : ((j - (Znth i al 0) ) >= 0)) (PreH2 : (j > 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (1 <= k)) (PreH8 : (k <= c_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= k)) (PreH13 : (1 <= (Znth i al 0))) (PreH14 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH15 : (0 < d)) (PreH16 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH17 : (c_pre <= (ListLib.sum (al)))) (PreH18 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= 10000000)) (PreH21 : (Forall (Z.le (1)) al )) (PreH22 : (Forall2 Z.le al bl )) (PreH23 : (Forall (Z.ge (10000)) bl )) (PreH24 : (Forall (Z.le (0)) dl )) (PreH25 : (Forall (Z.ge (10000001)) dl )) (PreH26 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) (PreH27 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ ((j - (Znth i al 0) ) >= 0) ” 
  &&  “ (j > 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 5000) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= c_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= k) ” 
  &&  “ (1 <= (Znth i al 0)) ” 
  &&  “ (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre )) ” 
  &&  “ (0 < d) ” 
  &&  “ (k = (c_pre - (FreeCash (c_pre) (al) (bl)) )) ” 
  &&  “ (c_pre <= (ListLib.sum (al))) ” 
  &&  “ (ans = (UnconstrainedRevenue (c_pre) (al) (bl))) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= 10000000) ” 
  &&  “ (Forall (Z.le (1)) al ) ” 
  &&  “ (Forall2 Z.le al bl ) ” 
  &&  “ (Forall (Z.ge (10000)) bl ) ” 
  &&  “ (Forall (Z.le (0)) dl ) ” 
  &&  “ (Forall (Z.ge (10000001)) dl ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) )) ” 
  &&  “ forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) )) ”
  &&  (((( &( "dp" ) ) + ((j - (Znth i al 0) ) * sizeof(INT)))) # Int  |-> (Znth (j - (Znth i al 0) ) dl 0))
  **  (IntArray.missing_i ( &( "dp" ) ) (j - (Znth i al 0) ) 0 (k + 1 ) dl )
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
.

Definition magic_items_partial_solve_wit_13 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : ((j - (Znth i al 0) ) < 0)) (PreH2 : (j > 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (1 <= k)) (PreH8 : (k <= c_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= k)) (PreH13 : (1 <= (Znth i al 0))) (PreH14 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH15 : (0 < d)) (PreH16 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH17 : (c_pre <= (ListLib.sum (al)))) (PreH18 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= 10000000)) (PreH21 : (Forall (Z.le (1)) al )) (PreH22 : (Forall2 Z.le al bl )) (PreH23 : (Forall (Z.ge (10000)) bl )) (PreH24 : (Forall (Z.le (0)) dl )) (PreH25 : (Forall (Z.ge (10000001)) dl )) (PreH26 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) (PreH27 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) ))) ,
  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ ((j - (Znth i al 0) ) < 0) ” 
  &&  “ (j > 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 5000) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= c_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= k) ” 
  &&  “ (1 <= (Znth i al 0)) ” 
  &&  “ (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre )) ” 
  &&  “ (0 < d) ” 
  &&  “ (k = (c_pre - (FreeCash (c_pre) (al) (bl)) )) ” 
  &&  “ (c_pre <= (ListLib.sum (al))) ” 
  &&  “ (ans = (UnconstrainedRevenue (c_pre) (al) (bl))) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= 10000000) ” 
  &&  “ (Forall (Z.le (1)) al ) ” 
  &&  “ (Forall2 Z.le al bl ) ” 
  &&  “ (Forall (Z.ge (10000)) bl ) ” 
  &&  “ (Forall (Z.le (0)) dl ) ” 
  &&  “ (Forall (Z.ge (10000001)) dl ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) )) ” 
  &&  “ forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) )) ”
  &&  (((( &( "dp" ) ) + (j * sizeof(INT)))) # Int  |-> (Znth j dl 0))
  **  (IntArray.missing_i ( &( "dp" ) ) j 0 (k + 1 ) dl )
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
.

Definition magic_items_partial_solve_wit_14 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : ((j - (Znth i al 0) ) >= 0)) (PreH2 : (j > 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 5000)) (PreH7 : (1 <= k)) (PreH8 : (k <= c_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= k)) (PreH13 : (1 <= (Znth i al 0))) (PreH14 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH15 : (0 < d)) (PreH16 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH17 : (c_pre <= (ListLib.sum (al)))) (PreH18 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH19 : (0 <= ans)) (PreH20 : (ans <= 10000000)) (PreH21 : (Forall (Z.le (1)) al )) (PreH22 : (Forall2 Z.le al bl )) (PreH23 : (Forall (Z.ge (10000)) bl )) (PreH24 : (Forall (Z.le (0)) dl )) (PreH25 : (Forall (Z.ge (10000001)) dl )) (PreH26 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) (PreH27 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) ))) ,
  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ ((j - (Znth i al 0) ) >= 0) ” 
  &&  “ (j > 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 5000) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= c_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= k) ” 
  &&  “ (1 <= (Znth i al 0)) ” 
  &&  “ (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre )) ” 
  &&  “ (0 < d) ” 
  &&  “ (k = (c_pre - (FreeCash (c_pre) (al) (bl)) )) ” 
  &&  “ (c_pre <= (ListLib.sum (al))) ” 
  &&  “ (ans = (UnconstrainedRevenue (c_pre) (al) (bl))) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= 10000000) ” 
  &&  “ (Forall (Z.le (1)) al ) ” 
  &&  “ (Forall2 Z.le al bl ) ” 
  &&  “ (Forall (Z.ge (10000)) bl ) ” 
  &&  “ (Forall (Z.le (0)) dl ) ” 
  &&  “ (Forall (Z.ge (10000001)) dl ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) )) ” 
  &&  “ forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) )) ”
  &&  (((( &( "dp" ) ) + (j * sizeof(INT)))) # Int  |-> (Znth j dl 0))
  **  (IntArray.missing_i ( &( "dp" ) ) j 0 (k + 1 ) dl )
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
.

Definition magic_items_partial_solve_wit_15 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (((Znth 0 dl 0) + d ) < (Znth j dl 0))) (PreH2 : ((j - (Znth i al 0) ) < 0)) (PreH3 : (j > 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 5000)) (PreH8 : (1 <= k)) (PreH9 : (k <= c_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= k)) (PreH14 : (1 <= (Znth i al 0))) (PreH15 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH16 : (0 < d)) (PreH17 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH18 : (c_pre <= (ListLib.sum (al)))) (PreH19 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= 10000000)) (PreH22 : (Forall (Z.le (1)) al )) (PreH23 : (Forall2 Z.le al bl )) (PreH24 : (Forall (Z.ge (10000)) bl )) (PreH25 : (Forall (Z.le (0)) dl )) (PreH26 : (Forall (Z.ge (10000001)) dl )) (PreH27 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) (PreH28 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) ))) ,
  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ (((Znth 0 dl 0) + d ) < (Znth j dl 0)) ” 
  &&  “ ((j - (Znth i al 0) ) < 0) ” 
  &&  “ (j > 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 5000) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= c_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= k) ” 
  &&  “ (1 <= (Znth i al 0)) ” 
  &&  “ (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre )) ” 
  &&  “ (0 < d) ” 
  &&  “ (k = (c_pre - (FreeCash (c_pre) (al) (bl)) )) ” 
  &&  “ (c_pre <= (ListLib.sum (al))) ” 
  &&  “ (ans = (UnconstrainedRevenue (c_pre) (al) (bl))) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= 10000000) ” 
  &&  “ (Forall (Z.le (1)) al ) ” 
  &&  “ (Forall2 Z.le al bl ) ” 
  &&  “ (Forall (Z.ge (10000)) bl ) ” 
  &&  “ (Forall (Z.le (0)) dl ) ” 
  &&  “ (Forall (Z.ge (10000001)) dl ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) )) ” 
  &&  “ forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) )) ”
  &&  (((( &( "dp" ) ) + (j * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "dp" ) ) j 0 (k + 1 ) dl )
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
.

Definition magic_items_partial_solve_wit_16 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (d: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (((Znth (j - (Znth i al 0) ) dl 0) + d ) < (Znth j dl 0))) (PreH2 : ((j - (Znth i al 0) ) >= 0)) (PreH3 : (j > 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 5000)) (PreH8 : (1 <= k)) (PreH9 : (k <= c_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= k)) (PreH14 : (1 <= (Znth i al 0))) (PreH15 : (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre ))) (PreH16 : (0 < d)) (PreH17 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH18 : (c_pre <= (ListLib.sum (al)))) (PreH19 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH20 : (0 <= ans)) (PreH21 : (ans <= 10000000)) (PreH22 : (Forall (Z.le (1)) al )) (PreH23 : (Forall2 Z.le al bl )) (PreH24 : (Forall (Z.ge (10000)) bl )) (PreH25 : (Forall (Z.le (0)) dl )) (PreH26 : (Forall (Z.ge (10000001)) dl )) (PreH27 : forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) (PreH28 : forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) ))) ,
  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ (((Znth (j - (Znth i al 0) ) dl 0) + d ) < (Znth j dl 0)) ” 
  &&  “ ((j - (Znth i al 0) ) >= 0) ” 
  &&  “ (j > 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 5000) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= c_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= k) ” 
  &&  “ (1 <= (Znth i al 0)) ” 
  &&  “ (d = (((Znth (i) (bl) (0)) - (Znth (i) (al) (0)) ) - c_pre )) ” 
  &&  “ (0 < d) ” 
  &&  “ (k = (c_pre - (FreeCash (c_pre) (al) (bl)) )) ” 
  &&  “ (c_pre <= (ListLib.sum (al))) ” 
  &&  “ (ans = (UnconstrainedRevenue (c_pre) (al) (bl))) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= 10000000) ” 
  &&  “ (Forall (Z.le (1)) al ) ” 
  &&  “ (Forall2 Z.le al bl ) ” 
  &&  “ (Forall (Z.ge (10000)) bl ) ” 
  &&  “ (Forall (Z.le (0)) dl ) ” 
  &&  “ (Forall (Z.ge (10000001)) dl ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= j)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) )) ” 
  &&  “ forall (q_2: Z) , (((j < q_2) /\ (q_2 <= k)) -> (MinimumSacrifice c_pre al bl (i + 1 ) q_2 (Znth (q_2) (dl) (0)) )) ”
  &&  (((( &( "dp" ) ) + (j * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "dp" ) ) j 0 (k + 1 ) dl )
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
.

Definition magic_items_partial_solve_wit_17 := 
forall (b_pre: Z) (a_pre: Z) (c_pre: Z) (n_pre: Z) (bl: (@list Z)) (al: (@list Z)) (dl: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 5000)) (PreH6 : (1 <= k)) (PreH7 : (k <= c_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (k = (c_pre - (FreeCash (c_pre) (al) (bl)) ))) (PreH11 : (c_pre <= (ListLib.sum (al)))) (PreH12 : (ans = (UnconstrainedRevenue (c_pre) (al) (bl)))) (PreH13 : (0 <= ans)) (PreH14 : (ans <= 10000000)) (PreH15 : (Forall (Z.le (1)) al )) (PreH16 : (Forall2 Z.le al bl )) (PreH17 : (Forall (Z.ge (10000)) bl )) (PreH18 : (Forall (Z.le (0)) dl )) (PreH19 : (Forall (Z.ge (10000001)) dl )) (PreH20 : forall (q: Z) , (((0 <= q) /\ (q <= k)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) ))) ,
  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.full ( &( "dp" ) ) (k + 1 ) dl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
|--
  “ (i >= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 5000) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= c_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (k = (c_pre - (FreeCash (c_pre) (al) (bl)) )) ” 
  &&  “ (c_pre <= (ListLib.sum (al))) ” 
  &&  “ (ans = (UnconstrainedRevenue (c_pre) (al) (bl))) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= 10000000) ” 
  &&  “ (Forall (Z.le (1)) al ) ” 
  &&  “ (Forall2 Z.le al bl ) ” 
  &&  “ (Forall (Z.ge (10000)) bl ) ” 
  &&  “ (Forall (Z.le (0)) dl ) ” 
  &&  “ (Forall (Z.ge (10000001)) dl ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q <= k)) -> (MinimumSacrifice c_pre al bl i q (Znth (q) (dl) (0)) )) ”
  &&  (((( &( "dp" ) ) + (k * sizeof(INT)))) # Int  |-> (Znth k dl 0))
  **  (IntArray.missing_i ( &( "dp" ) ) k 0 (k + 1 ) dl )
  **  (IntArray.full a_pre n_pre al )
  **  (IntArray.full b_pre n_pre bl )
  **  (IntArray.undef_seg ( &( "dp" ) ) (k + 1 ) 5001 )
.

Module Type VC_Correct.


Axiom proof_of_magic_items_safety_wit_1 : magic_items_safety_wit_1.
Axiom proof_of_magic_items_safety_wit_2 : magic_items_safety_wit_2.
Axiom proof_of_magic_items_safety_wit_3 : magic_items_safety_wit_3.
Axiom proof_of_magic_items_safety_wit_4 : magic_items_safety_wit_4.
Axiom proof_of_magic_items_safety_wit_5 : magic_items_safety_wit_5.
Axiom proof_of_magic_items_safety_wit_6 : magic_items_safety_wit_6.
Axiom proof_of_magic_items_safety_wit_7 : magic_items_safety_wit_7.
Axiom proof_of_magic_items_safety_wit_8 : magic_items_safety_wit_8.
Axiom proof_of_magic_items_safety_wit_9 : magic_items_safety_wit_9.
Axiom proof_of_magic_items_safety_wit_10 : magic_items_safety_wit_10.
Axiom proof_of_magic_items_safety_wit_11 : magic_items_safety_wit_11.
Axiom proof_of_magic_items_safety_wit_12 : magic_items_safety_wit_12.
Axiom proof_of_magic_items_safety_wit_13 : magic_items_safety_wit_13.
Axiom proof_of_magic_items_safety_wit_14 : magic_items_safety_wit_14.
Axiom proof_of_magic_items_safety_wit_15 : magic_items_safety_wit_15.
Axiom proof_of_magic_items_safety_wit_16 : magic_items_safety_wit_16.
Axiom proof_of_magic_items_safety_wit_17 : magic_items_safety_wit_17.
Axiom proof_of_magic_items_safety_wit_18 : magic_items_safety_wit_18.
Axiom proof_of_magic_items_safety_wit_19 : magic_items_safety_wit_19.
Axiom proof_of_magic_items_safety_wit_20 : magic_items_safety_wit_20.
Axiom proof_of_magic_items_safety_wit_21 : magic_items_safety_wit_21.
Axiom proof_of_magic_items_safety_wit_22 : magic_items_safety_wit_22.
Axiom proof_of_magic_items_safety_wit_23 : magic_items_safety_wit_23.
Axiom proof_of_magic_items_safety_wit_24 : magic_items_safety_wit_24.
Axiom proof_of_magic_items_safety_wit_25 : magic_items_safety_wit_25.
Axiom proof_of_magic_items_safety_wit_26 : magic_items_safety_wit_26.
Axiom proof_of_magic_items_safety_wit_27 : magic_items_safety_wit_27.
Axiom proof_of_magic_items_safety_wit_28 : magic_items_safety_wit_28.
Axiom proof_of_magic_items_safety_wit_29 : magic_items_safety_wit_29.
Axiom proof_of_magic_items_safety_wit_30 : magic_items_safety_wit_30.
Axiom proof_of_magic_items_safety_wit_31 : magic_items_safety_wit_31.
Axiom proof_of_magic_items_safety_wit_32 : magic_items_safety_wit_32.
Axiom proof_of_magic_items_safety_wit_33 : magic_items_safety_wit_33.
Axiom proof_of_magic_items_safety_wit_34 : magic_items_safety_wit_34.
Axiom proof_of_magic_items_safety_wit_35 : magic_items_safety_wit_35.
Axiom proof_of_magic_items_safety_wit_36 : magic_items_safety_wit_36.
Axiom proof_of_magic_items_entail_wit_1 : magic_items_entail_wit_1.
Axiom proof_of_magic_items_entail_wit_2_1 : magic_items_entail_wit_2_1.
Axiom proof_of_magic_items_entail_wit_2_2 : magic_items_entail_wit_2_2.
Axiom proof_of_magic_items_entail_wit_3 : magic_items_entail_wit_3.
Axiom proof_of_magic_items_entail_wit_4 : magic_items_entail_wit_4.
Axiom proof_of_magic_items_entail_wit_5 : magic_items_entail_wit_5.
Axiom proof_of_magic_items_entail_wit_6 : magic_items_entail_wit_6.
Axiom proof_of_magic_items_entail_wit_7_1 : magic_items_entail_wit_7_1.
Axiom proof_of_magic_items_entail_wit_7_2 : magic_items_entail_wit_7_2.
Axiom proof_of_magic_items_entail_wit_7_3 : magic_items_entail_wit_7_3.
Axiom proof_of_magic_items_entail_wit_7_4 : magic_items_entail_wit_7_4.
Axiom proof_of_magic_items_entail_wit_8_1 : magic_items_entail_wit_8_1.
Axiom proof_of_magic_items_entail_wit_8_2 : magic_items_entail_wit_8_2.
Axiom proof_of_magic_items_entail_wit_9 : magic_items_entail_wit_9.
Axiom proof_of_magic_items_return_wit_1 : magic_items_return_wit_1.
Axiom proof_of_magic_items_return_wit_2 : magic_items_return_wit_2.
Axiom proof_of_magic_items_return_wit_3 : magic_items_return_wit_3.
Axiom proof_of_magic_items_partial_solve_wit_1 : magic_items_partial_solve_wit_1.
Axiom proof_of_magic_items_partial_solve_wit_2 : magic_items_partial_solve_wit_2.
Axiom proof_of_magic_items_partial_solve_wit_3 : magic_items_partial_solve_wit_3.
Axiom proof_of_magic_items_partial_solve_wit_4 : magic_items_partial_solve_wit_4.
Axiom proof_of_magic_items_partial_solve_wit_5 : magic_items_partial_solve_wit_5.
Axiom proof_of_magic_items_partial_solve_wit_6 : magic_items_partial_solve_wit_6.
Axiom proof_of_magic_items_partial_solve_wit_7 : magic_items_partial_solve_wit_7.
Axiom proof_of_magic_items_partial_solve_wit_8 : magic_items_partial_solve_wit_8.
Axiom proof_of_magic_items_partial_solve_wit_9 : magic_items_partial_solve_wit_9.
Axiom proof_of_magic_items_partial_solve_wit_10 : magic_items_partial_solve_wit_10.
Axiom proof_of_magic_items_partial_solve_wit_11 : magic_items_partial_solve_wit_11.
Axiom proof_of_magic_items_partial_solve_wit_12 : magic_items_partial_solve_wit_12.
Axiom proof_of_magic_items_partial_solve_wit_13 : magic_items_partial_solve_wit_13.
Axiom proof_of_magic_items_partial_solve_wit_14 : magic_items_partial_solve_wit_14.
Axiom proof_of_magic_items_partial_solve_wit_15 : magic_items_partial_solve_wit_15.
Axiom proof_of_magic_items_partial_solve_wit_16 : magic_items_partial_solve_wit_16.
Axiom proof_of_magic_items_partial_solve_wit_17 : magic_items_partial_solve_wit_17.

End VC_Correct.
