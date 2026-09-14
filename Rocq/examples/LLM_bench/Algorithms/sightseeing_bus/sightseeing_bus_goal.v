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
Require Import SimpleC.EE.LLM_bench.Algorithms.sightseeing_bus.sightseeing_bus_lib.
Local Open Scope sac.

(*----- Function solve -----*)

Definition solve_safety_wit_1 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (PreH1 : (0 <= k_pre)) (PreH2 : (k_pre <= 100000)) (PreH3 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) ,
  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.undef_full late_pre n_pre )
  **  (IntArray.undef_full off_pre n_pre )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_2 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_prefix: (@list Z)) (latest_prefix: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (latest_prefix)) = i)) (PreH5 : ((Zlength (counts_prefix)) = i)) (PreH6 : (WorkspacesZeroPrefix latest_prefix counts_prefix i )) (PreH7 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH8 : (0 <= k_pre)) (PreH9 : (k_pre <= 100000)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.seg late_pre 0 i latest_prefix )
  **  (IntArray.undef_seg late_pre i n_pre )
  **  (IntArray.seg off_pre 0 i counts_prefix )
  **  (IntArray.undef_seg off_pre i n_pre )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_3 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_prefix: (@list Z)) (latest_prefix: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (latest_prefix)) = i)) (PreH5 : ((Zlength (counts_prefix)) = i)) (PreH6 : (WorkspacesZeroPrefix latest_prefix counts_prefix i )) (PreH7 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH8 : (0 <= k_pre)) (PreH9 : (k_pre <= 100000)) ,
  (IntArray.seg late_pre 0 (i + 1 ) (app (latest_prefix) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg late_pre (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.seg off_pre 0 i counts_prefix )
  **  (IntArray.undef_seg off_pre i n_pre )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_4 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_prefix: (@list Z)) (latest_prefix: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (latest_prefix)) = i)) (PreH5 : ((Zlength (counts_prefix)) = i)) (PreH6 : (WorkspacesZeroPrefix latest_prefix counts_prefix i )) (PreH7 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH8 : (0 <= k_pre)) (PreH9 : (k_pre <= 100000)) ,
  (IntArray.seg off_pre 0 (i + 1 ) (app (counts_prefix) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg off_pre (i + 1 ) n_pre )
  **  (IntArray.seg late_pre 0 (i + 1 ) (app (latest_prefix) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg late_pre (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_5 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (PreH1 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 100000)) (PreH4 : ((Zlength (latest)) = n_pre)) (PreH5 : ((Zlength (counts)) = n_pre)) (PreH6 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)))) (PreH7 : (PassengerAggregationPrefix n_pre m_pre times origins destinations 0 latest counts )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "i" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_6 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : ((Zlength (latest)) = n_pre)) (PreH8 : ((Zlength (counts)) = n_pre)) (PreH9 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH10 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full a_pre m_pre origins )
  **  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ (((Znth i origins 0) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i origins 0) - 1 )) ”
) \/
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : ((Zlength (latest)) = n_pre)) (PreH8 : ((Zlength (counts)) = n_pre)) (PreH9 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH10 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full a_pre m_pre origins )
  **  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ (((Znth i origins 0) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i origins 0) - 1 )) ”
).

Definition solve_safety_wit_6_split_goal_1 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : ((Zlength (latest)) = n_pre)) (PreH8 : ((Zlength (counts)) = n_pre)) (PreH9 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH10 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full a_pre m_pre origins )
  **  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ (((Znth i origins 0) - 1 ) <= INT_MAX) ”
.

Definition solve_safety_wit_6_split_goal_2 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : ((Zlength (latest)) = n_pre)) (PreH8 : ((Zlength (counts)) = n_pre)) (PreH9 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH10 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full a_pre m_pre origins )
  **  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ ((INT_MIN) <= ((Znth i origins 0) - 1 )) ”
.

Definition solve_safety_wit_7 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : ((Zlength (latest)) = n_pre)) (PreH8 : ((Zlength (counts)) = n_pre)) (PreH9 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH10 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full a_pre m_pre origins )
  **  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_8 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : ((Zlength (latest)) = n_pre)) (PreH8 : ((Zlength (counts)) = n_pre)) (PreH9 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH10 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full b_pre m_pre destinations )
  **  ((( &( "y" ) )) # Int  |->_)
  **  (IntArray.full a_pre m_pre origins )
  **  ((( &( "x" ) )) # Int  |-> ((Znth i origins 0) - 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ (((Znth i destinations 0) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i destinations 0) - 1 )) ”
) \/
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : ((Zlength (latest)) = n_pre)) (PreH8 : ((Zlength (counts)) = n_pre)) (PreH9 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH10 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full b_pre m_pre destinations )
  **  ((( &( "y" ) )) # Int  |->_)
  **  (IntArray.full a_pre m_pre origins )
  **  ((( &( "x" ) )) # Int  |-> ((Znth i origins 0) - 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ (((Znth i destinations 0) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i destinations 0) - 1 )) ”
).

Definition solve_safety_wit_8_split_goal_1 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : ((Zlength (latest)) = n_pre)) (PreH8 : ((Zlength (counts)) = n_pre)) (PreH9 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH10 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full b_pre m_pre destinations )
  **  ((( &( "y" ) )) # Int  |->_)
  **  (IntArray.full a_pre m_pre origins )
  **  ((( &( "x" ) )) # Int  |-> ((Znth i origins 0) - 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ (((Znth i destinations 0) - 1 ) <= INT_MAX) ”
.

Definition solve_safety_wit_8_split_goal_2 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : ((Zlength (latest)) = n_pre)) (PreH8 : ((Zlength (counts)) = n_pre)) (PreH9 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH10 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full b_pre m_pre destinations )
  **  ((( &( "y" ) )) # Int  |->_)
  **  (IntArray.full a_pre m_pre origins )
  **  ((( &( "x" ) )) # Int  |-> ((Znth i origins 0) - 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ ((INT_MIN) <= ((Znth i destinations 0) - 1 )) ”
.

Definition solve_safety_wit_9 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : ((Zlength (latest)) = n_pre)) (PreH8 : ((Zlength (counts)) = n_pre)) (PreH9 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH10 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full b_pre m_pre destinations )
  **  ((( &( "y" ) )) # Int  |->_)
  **  (IntArray.full a_pre m_pre origins )
  **  ((( &( "x" ) )) # Int  |-> ((Znth i origins 0) - 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_10 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) < (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH3 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH4 : (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX)) (PreH5 : (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN)) (PreH6 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH7 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH16 : (i < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= 100000)) (PreH22 : ((Zlength (latest)) = n_pre)) (PreH23 : ((Zlength (counts)) = n_pre)) (PreH24 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH25 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full late_pre n_pre (replace_Znth (((Znth (i) (origins) (0)) - 1 )) ((Znth i times 0)) (latest)) )
  **  (IntArray.full t_pre m_pre times )
  **  ((( &( "y" ) )) # Int  |-> ((Znth (i) (destinations) (0)) - 1 ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> ((Znth (i) (origins) (0)) - 1 ))
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth ((Znth (i) (destinations) (0)) - 1 ) counts 0) + 1 )) ”
) \/
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) < (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH3 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH4 : (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX)) (PreH5 : (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN)) (PreH6 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH7 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH16 : (i < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= 100000)) (PreH22 : ((Zlength (latest)) = n_pre)) (PreH23 : ((Zlength (counts)) = n_pre)) (PreH24 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH25 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full late_pre n_pre (replace_Znth (((Znth (i) (origins) (0)) - 1 )) ((Znth i times 0)) (latest)) )
  **  (IntArray.full t_pre m_pre times )
  **  ((( &( "y" ) )) # Int  |-> ((Znth (i) (destinations) (0)) - 1 ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> ((Znth (i) (origins) (0)) - 1 ))
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth ((Znth (i) (destinations) (0)) - 1 ) counts 0) + 1 )) ”
).

Definition solve_safety_wit_10_split_goal_1 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) < (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH3 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH4 : (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX)) (PreH5 : (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN)) (PreH6 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH7 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH16 : (i < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= 100000)) (PreH22 : ((Zlength (latest)) = n_pre)) (PreH23 : ((Zlength (counts)) = n_pre)) (PreH24 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH25 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full late_pre n_pre (replace_Znth (((Znth (i) (origins) (0)) - 1 )) ((Znth i times 0)) (latest)) )
  **  (IntArray.full t_pre m_pre times )
  **  ((( &( "y" ) )) # Int  |-> ((Znth (i) (destinations) (0)) - 1 ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> ((Znth (i) (origins) (0)) - 1 ))
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts 0) + 1 ) <= INT_MAX) ”
.

Definition solve_safety_wit_10_split_goal_2 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) < (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH3 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH4 : (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX)) (PreH5 : (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN)) (PreH6 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH7 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH16 : (i < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= 100000)) (PreH22 : ((Zlength (latest)) = n_pre)) (PreH23 : ((Zlength (counts)) = n_pre)) (PreH24 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH25 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full late_pre n_pre (replace_Znth (((Znth (i) (origins) (0)) - 1 )) ((Znth i times 0)) (latest)) )
  **  (IntArray.full t_pre m_pre times )
  **  ((( &( "y" ) )) # Int  |-> ((Znth (i) (destinations) (0)) - 1 ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> ((Znth (i) (origins) (0)) - 1 ))
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ ((INT_MIN) <= ((Znth ((Znth (i) (destinations) (0)) - 1 ) counts 0) + 1 )) ”
.

Definition solve_safety_wit_11 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) < (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH3 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH4 : (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX)) (PreH5 : (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN)) (PreH6 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH7 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH16 : (i < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= 100000)) (PreH22 : ((Zlength (latest)) = n_pre)) (PreH23 : ((Zlength (counts)) = n_pre)) (PreH24 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH25 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full late_pre n_pre (replace_Znth (((Znth (i) (origins) (0)) - 1 )) ((Znth i times 0)) (latest)) )
  **  (IntArray.full t_pre m_pre times )
  **  ((( &( "y" ) )) # Int  |-> ((Znth (i) (destinations) (0)) - 1 ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> ((Znth (i) (origins) (0)) - 1 ))
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_12 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) >= (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH3 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH4 : (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX)) (PreH5 : (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN)) (PreH6 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH7 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH16 : (i < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= 100000)) (PreH22 : ((Zlength (latest)) = n_pre)) (PreH23 : ((Zlength (counts)) = n_pre)) (PreH24 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH25 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full late_pre n_pre latest )
  **  ((( &( "y" ) )) # Int  |-> ((Znth (i) (destinations) (0)) - 1 ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> ((Znth (i) (origins) (0)) - 1 ))
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth ((Znth (i) (destinations) (0)) - 1 ) counts 0) + 1 )) ”
) \/
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) >= (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH3 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH4 : (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX)) (PreH5 : (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN)) (PreH6 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH7 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH16 : (i < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= 100000)) (PreH22 : ((Zlength (latest)) = n_pre)) (PreH23 : ((Zlength (counts)) = n_pre)) (PreH24 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH25 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full late_pre n_pre latest )
  **  ((( &( "y" ) )) # Int  |-> ((Znth (i) (destinations) (0)) - 1 ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> ((Znth (i) (origins) (0)) - 1 ))
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth ((Znth (i) (destinations) (0)) - 1 ) counts 0) + 1 )) ”
).

Definition solve_safety_wit_12_split_goal_1 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) >= (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH3 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH4 : (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX)) (PreH5 : (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN)) (PreH6 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH7 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH16 : (i < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= 100000)) (PreH22 : ((Zlength (latest)) = n_pre)) (PreH23 : ((Zlength (counts)) = n_pre)) (PreH24 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH25 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full late_pre n_pre latest )
  **  ((( &( "y" ) )) # Int  |-> ((Znth (i) (destinations) (0)) - 1 ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> ((Znth (i) (origins) (0)) - 1 ))
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts 0) + 1 ) <= INT_MAX) ”
.

Definition solve_safety_wit_12_split_goal_2 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) >= (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH3 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH4 : (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX)) (PreH5 : (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN)) (PreH6 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH7 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH16 : (i < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= 100000)) (PreH22 : ((Zlength (latest)) = n_pre)) (PreH23 : ((Zlength (counts)) = n_pre)) (PreH24 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH25 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full late_pre n_pre latest )
  **  ((( &( "y" ) )) # Int  |-> ((Znth (i) (destinations) (0)) - 1 ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> ((Znth (i) (origins) (0)) - 1 ))
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ ((INT_MIN) <= ((Znth ((Znth (i) (destinations) (0)) - 1 ) counts 0) + 1 )) ”
.

Definition solve_safety_wit_13 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) >= (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH3 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH4 : (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX)) (PreH5 : (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN)) (PreH6 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH7 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH16 : (i < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= 100000)) (PreH22 : ((Zlength (latest)) = n_pre)) (PreH23 : ((Zlength (counts)) = n_pre)) (PreH24 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH25 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full late_pre n_pre latest )
  **  ((( &( "y" ) )) # Int  |-> ((Znth (i) (destinations) (0)) - 1 ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> ((Znth (i) (origins) (0)) - 1 ))
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_14 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) < (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH3 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH4 : (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX)) (PreH5 : (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN)) (PreH6 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH7 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH16 : (i < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= 100000)) (PreH22 : ((Zlength (latest)) = n_pre)) (PreH23 : ((Zlength (counts)) = n_pre)) (PreH24 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH25 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full off_pre n_pre (replace_Znth (((Znth (i) (destinations) (0)) - 1 )) (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts 0) + 1 )) (counts)) )
  **  (IntArray.full late_pre n_pre (replace_Znth (((Znth (i) (origins) (0)) - 1 )) ((Znth i times 0)) (latest)) )
  **  (IntArray.full t_pre m_pre times )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_15 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) >= (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH3 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH4 : (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX)) (PreH5 : (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN)) (PreH6 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH7 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH16 : (i < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= 100000)) (PreH22 : ((Zlength (latest)) = n_pre)) (PreH23 : ((Zlength (counts)) = n_pre)) (PreH24 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH25 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full off_pre n_pre (replace_Znth (((Znth (i) (destinations) (0)) - 1 )) (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts 0) + 1 )) (counts)) )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full late_pre n_pre latest )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_16 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (PreH1 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 100000)) (PreH4 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH5 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "i" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_17 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (PreH1 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 100000)) (PreH4 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH5 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "i" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |-> 0)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_18 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : (cur >= (Znth i latest 0))) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= cur)) (PreH6 : (cur <= 200000)) (PreH7 : ((Zlength (arrivals_prefix)) = i)) (PreH8 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= 100000)) (PreH11 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH12 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)))) (PreH13 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full late_pre n_pre latest )
  **  (IntArray.seg arr_pre 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg arr_pre (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_19 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : (cur < (Znth i latest 0))) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= cur)) (PreH6 : (cur <= 200000)) (PreH7 : ((Zlength (arrivals_prefix)) = i)) (PreH8 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= 100000)) (PreH11 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH12 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)))) (PreH13 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full late_pre n_pre latest )
  **  (IntArray.seg arr_pre 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg arr_pre (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i latest 0))
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_20 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : (cur < (Znth i latest 0))) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= cur)) (PreH6 : (cur <= 200000)) (PreH7 : ((Zlength (arrivals_prefix)) = i)) (PreH8 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= 100000)) (PreH11 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH12 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)))) (PreH13 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full late_pre n_pre latest )
  **  (IntArray.seg arr_pre 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg arr_pre (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i latest 0))
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_21 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : (cur >= (Znth i latest 0))) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= cur)) (PreH6 : (cur <= 200000)) (PreH7 : ((Zlength (arrivals_prefix)) = i)) (PreH8 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= 100000)) (PreH11 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH12 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)))) (PreH13 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full late_pre n_pre latest )
  **  (IntArray.seg arr_pre 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg arr_pre (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_22 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur < (Znth i latest 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix)) = i)) (PreH9 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= 100000)) (PreH12 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)))) (PreH14 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.seg arr_pre 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg arr_pre (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i latest 0))
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ (((Znth i latest 0) + (Znth i dist 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i latest 0) + (Znth i dist 0) )) ”
) \/
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur < (Znth i latest 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix)) = i)) (PreH9 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= 100000)) (PreH12 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)))) (PreH14 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.seg arr_pre 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg arr_pre (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i latest 0))
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ (((Znth i latest 0) + (Znth i dist 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i latest 0) + (Znth i dist 0) )) ”
).

Definition solve_safety_wit_22_split_goal_1 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur < (Znth i latest 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix)) = i)) (PreH9 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= 100000)) (PreH12 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)))) (PreH14 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.seg arr_pre 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg arr_pre (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i latest 0))
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ (((Znth i latest 0) + (Znth i dist 0) ) <= INT_MAX) ”
.

Definition solve_safety_wit_22_split_goal_2 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur < (Znth i latest 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix)) = i)) (PreH9 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= 100000)) (PreH12 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)))) (PreH14 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.seg arr_pre 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg arr_pre (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i latest 0))
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ ((INT_MIN) <= ((Znth i latest 0) + (Znth i dist 0) )) ”
.

Definition solve_safety_wit_23 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur >= (Znth i latest 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix)) = i)) (PreH9 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= 100000)) (PreH12 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)))) (PreH14 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.seg arr_pre 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg arr_pre (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ ((cur + (Znth i dist 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cur + (Znth i dist 0) )) ”
) \/
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur >= (Znth i latest 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix)) = i)) (PreH9 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= 100000)) (PreH12 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)))) (PreH14 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.seg arr_pre 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg arr_pre (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ ((cur + (Znth i dist 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cur + (Znth i dist 0) )) ”
).

Definition solve_safety_wit_23_split_goal_1 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur >= (Znth i latest 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix)) = i)) (PreH9 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= 100000)) (PreH12 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)))) (PreH14 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.seg arr_pre 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg arr_pre (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ ((cur + (Znth i dist 0) ) <= INT_MAX) ”
.

Definition solve_safety_wit_23_split_goal_2 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur >= (Znth i latest 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix)) = i)) (PreH9 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= 100000)) (PreH12 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)))) (PreH14 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.seg arr_pre 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg arr_pre (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ ((INT_MIN) <= (cur + (Znth i dist 0) )) ”
.

Definition solve_safety_wit_24 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur < (Znth i latest 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix)) = i)) (PreH9 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= 100000)) (PreH12 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)))) (PreH14 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.seg arr_pre 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg arr_pre (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cur" ) )) # Int  |-> ((Znth i latest 0) + (Znth i dist 0) ))
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_25 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur >= (Znth i latest 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix)) = i)) (PreH9 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= 100000)) (PreH12 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)))) (PreH14 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.seg arr_pre 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg arr_pre (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cur" ) )) # Int  |-> (cur + (Znth i dist 0) ))
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_26 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (cur < (Znth i latest 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix)) = i)) (PreH9 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= 100000)) (PreH12 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)))) (PreH14 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full late_pre n_pre latest )
  **  (IntArray.seg arr_pre 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg arr_pre (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i latest 0))
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_27 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (cur >= (Znth i latest 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix)) = i)) (PreH9 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= 100000)) (PreH12 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)))) (PreH14 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full late_pre n_pre latest )
  **  (IntArray.seg arr_pre 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg arr_pre (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_28 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (k: Z) (PreH1 : (0 <= k)) (PreH2 : (k <= k_pre)) (PreH3 : (k_pre <= 100000)) (PreH4 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH5 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH6 : ((Zlength (latest)) = n_pre)) (PreH7 : ((Zlength (counts)) = n_pre)) (PreH8 : ((Zlength (arrivals)) = n_pre)) (PreH9 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH10 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH11 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_29 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (k: Z) (PreH1 : (k > 0)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH6 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH7 : ((Zlength (latest)) = n_pre)) (PreH8 : ((Zlength (counts)) = n_pre)) (PreH9 : ((Zlength (arrivals)) = n_pre)) (PreH10 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH11 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH12 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_30 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (k: Z) (PreH1 : (k > 0)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH6 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH7 : ((Zlength (latest)) = n_pre)) (PreH8 : ((Zlength (counts)) = n_pre)) (PreH9 : ((Zlength (arrivals)) = n_pre)) (PreH10 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH11 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH12 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |-> 0)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solve_safety_wit_31 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (k: Z) (PreH1 : (k > 0)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH6 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH7 : ((Zlength (latest)) = n_pre)) (PreH8 : ((Zlength (counts)) = n_pre)) (PreH9 : ((Zlength (arrivals)) = n_pre)) (PreH10 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH11 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH12 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |-> 0)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_32 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (k: Z) (PreH1 : (k > 0)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH6 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH7 : ((Zlength (latest)) = n_pre)) (PreH8 : ((Zlength (counts)) = n_pre)) (PreH9 : ((Zlength (arrivals)) = n_pre)) (PreH10 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH11 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH12 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |-> 0)
  **  ((( &( "pos" ) )) # Int  |-> (-1))
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_33 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (0 < k)) (PreH2 : (k <= k_pre)) (PreH3 : (k_pre <= 100000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 1 ))) (PreH6 : (0 <= best)) (PreH7 : (best <= m_pre)) (PreH8 : ((-1) <= pos)) (PreH9 : (pos < i)) (PreH10 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH11 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH12 : ((Zlength (latest)) = n_pre)) (PreH13 : ((Zlength (counts)) = n_pre)) (PreH14 : ((Zlength (arrivals)) = n_pre)) (PreH15 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH16 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH17 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH18 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_34 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (0 < k)) (PreH2 : (k <= k_pre)) (PreH3 : (k_pre <= 100000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 1 ))) (PreH6 : (0 <= best)) (PreH7 : (best <= m_pre)) (PreH8 : ((-1) <= pos)) (PreH9 : (pos < i)) (PreH10 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH11 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH12 : ((Zlength (latest)) = n_pre)) (PreH13 : ((Zlength (counts)) = n_pre)) (PreH14 : ((Zlength (arrivals)) = n_pre)) (PreH15 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH16 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH17 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH18 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_35 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n_pre - 1 ))) (PreH7 : (0 <= best)) (PreH8 : (best <= m_pre)) (PreH9 : ((-1) <= pos)) (PreH10 : (pos < i)) (PreH11 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH12 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH13 : ((Zlength (latest)) = n_pre)) (PreH14 : ((Zlength (counts)) = n_pre)) (PreH15 : ((Zlength (arrivals)) = n_pre)) (PreH16 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH17 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH18 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH19 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_36 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : ((Znth i current_dist 0) > 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (latest)) = n_pre)) (PreH15 : ((Zlength (counts)) = n_pre)) (PreH16 : ((Zlength (arrivals)) = n_pre)) (PreH17 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH18 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH19 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH20 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_37 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : ((Znth i current_dist 0) > 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (latest)) = n_pre)) (PreH15 : ((Zlength (counts)) = n_pre)) (PreH16 : ((Zlength (arrivals)) = n_pre)) (PreH17 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH18 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH19 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH20 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_38 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : ((Znth i current_dist 0) > 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (latest)) = n_pre)) (PreH15 : ((Zlength (counts)) = n_pre)) (PreH16 : ((Zlength (arrivals)) = n_pre)) (PreH17 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH18 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH19 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH20 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_39 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (j < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt <= m_pre)) (PreH11 : (0 <= best)) (PreH12 : (best <= m_pre)) (PreH13 : ((-1) <= pos)) (PreH14 : (pos < i)) (PreH15 : (0 < (Znth (i) (current_dist) (0)))) (PreH16 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH17 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH18 : ((Zlength (latest)) = n_pre)) (PreH19 : ((Zlength (counts)) = n_pre)) (PreH20 : ((Zlength (arrivals)) = n_pre)) (PreH21 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH22 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH23 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH24 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) (PreH25 : (MarginalBenefitScan counts latest arrivals i j cnt )) ,
  (IntArray.full off_pre n_pre counts )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ ((cnt + (Znth j counts 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cnt + (Znth j counts 0) )) ”
) \/
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (j < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt <= m_pre)) (PreH11 : (0 <= best)) (PreH12 : (best <= m_pre)) (PreH13 : ((-1) <= pos)) (PreH14 : (pos < i)) (PreH15 : (0 < (Znth (i) (current_dist) (0)))) (PreH16 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH17 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH18 : ((Zlength (latest)) = n_pre)) (PreH19 : ((Zlength (counts)) = n_pre)) (PreH20 : ((Zlength (arrivals)) = n_pre)) (PreH21 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH22 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH23 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH24 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) (PreH25 : (MarginalBenefitScan counts latest arrivals i j cnt )) ,
  (IntArray.full off_pre n_pre counts )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ ((cnt + (Znth j counts 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cnt + (Znth j counts 0) )) ”
).

Definition solve_safety_wit_39_split_goal_1 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (j < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt <= m_pre)) (PreH11 : (0 <= best)) (PreH12 : (best <= m_pre)) (PreH13 : ((-1) <= pos)) (PreH14 : (pos < i)) (PreH15 : (0 < (Znth (i) (current_dist) (0)))) (PreH16 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH17 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH18 : ((Zlength (latest)) = n_pre)) (PreH19 : ((Zlength (counts)) = n_pre)) (PreH20 : ((Zlength (arrivals)) = n_pre)) (PreH21 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH22 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH23 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH24 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) (PreH25 : (MarginalBenefitScan counts latest arrivals i j cnt )) ,
  (IntArray.full off_pre n_pre counts )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ ((cnt + (Znth j counts 0) ) <= INT_MAX) ”
.

Definition solve_safety_wit_39_split_goal_2 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (j < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt <= m_pre)) (PreH11 : (0 <= best)) (PreH12 : (best <= m_pre)) (PreH13 : ((-1) <= pos)) (PreH14 : (pos < i)) (PreH15 : (0 < (Znth (i) (current_dist) (0)))) (PreH16 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH17 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH18 : ((Zlength (latest)) = n_pre)) (PreH19 : ((Zlength (counts)) = n_pre)) (PreH20 : ((Zlength (arrivals)) = n_pre)) (PreH21 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH22 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH23 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH24 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) (PreH25 : (MarginalBenefitScan counts latest arrivals i j cnt )) ,
  (IntArray.full off_pre n_pre counts )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ ((INT_MIN) <= (cnt + (Znth j counts 0) )) ”
.

Definition solve_safety_wit_40 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : ((Znth j arrivals 0) > (Znth j latest 0))) (PreH2 : (j < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i < (n_pre - 1 ))) (PreH8 : ((i + 1 ) <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (0 <= cnt)) (PreH11 : (cnt <= m_pre)) (PreH12 : (0 <= best)) (PreH13 : (best <= m_pre)) (PreH14 : ((-1) <= pos)) (PreH15 : (pos < i)) (PreH16 : (0 < (Znth (i) (current_dist) (0)))) (PreH17 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH18 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH19 : ((Zlength (latest)) = n_pre)) (PreH20 : ((Zlength (counts)) = n_pre)) (PreH21 : ((Zlength (arrivals)) = n_pre)) (PreH22 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH24 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH25 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) (PreH26 : (MarginalBenefitScan counts latest arrivals i j cnt )) ,
  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full arr_pre n_pre arrivals )
  **  (IntArray.full off_pre n_pre counts )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "cnt" ) )) # Int  |-> (cnt + (Znth j counts 0) ))
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solve_safety_wit_41 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best < cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist) (0)))) (PreH16 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH17 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH18 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) (PreH19 : (EdgeMarginalBenefit n_pre counts latest arrivals i cnt )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "best" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_42 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best >= cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist) (0)))) (PreH16 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH17 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH18 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) (PreH19 : (EdgeMarginalBenefit n_pre counts latest arrivals i cnt )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_43 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : ((Znth i current_dist 0) <= 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (latest)) = n_pre)) (PreH15 : ((Zlength (counts)) = n_pre)) (PreH16 : ((Zlength (arrivals)) = n_pre)) (PreH17 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH18 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH19 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH20 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_44 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n_pre - 1 ))) (PreH7 : (0 <= best)) (PreH8 : (best <= m_pre)) (PreH9 : ((-1) <= pos)) (PreH10 : (pos < i)) (PreH11 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH12 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH13 : ((Zlength (latest)) = n_pre)) (PreH14 : ((Zlength (counts)) = n_pre)) (PreH15 : ((Zlength (arrivals)) = n_pre)) (PreH16 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH17 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH18 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH19 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_45 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (pos >= 0)) (PreH2 : ((i + 1 ) >= n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (latest)) = n_pre)) (PreH15 : ((Zlength (counts)) = n_pre)) (PreH16 : ((Zlength (arrivals)) = n_pre)) (PreH17 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH18 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH19 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH20 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_46 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best <> 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH14 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH15 : ((Zlength (latest)) = n_pre)) (PreH16 : ((Zlength (counts)) = n_pre)) (PreH17 : ((Zlength (arrivals)) = n_pre)) (PreH18 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH19 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH20 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH21 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ (((Znth pos current_dist 0) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth pos current_dist 0) - 1 )) ”
) \/
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best <> 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH14 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH15 : ((Zlength (latest)) = n_pre)) (PreH16 : ((Zlength (counts)) = n_pre)) (PreH17 : ((Zlength (arrivals)) = n_pre)) (PreH18 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH19 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH20 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH21 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ (((Znth pos current_dist 0) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth pos current_dist 0) - 1 )) ”
).

Definition solve_safety_wit_46_split_goal_1 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best <> 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH14 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH15 : ((Zlength (latest)) = n_pre)) (PreH16 : ((Zlength (counts)) = n_pre)) (PreH17 : ((Zlength (arrivals)) = n_pre)) (PreH18 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH19 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH20 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH21 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ (((Znth pos current_dist 0) - 1 ) <= INT_MAX) ”
.

Definition solve_safety_wit_46_split_goal_2 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best <> 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH14 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH15 : ((Zlength (latest)) = n_pre)) (PreH16 : ((Zlength (counts)) = n_pre)) (PreH17 : ((Zlength (arrivals)) = n_pre)) (PreH18 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH19 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH20 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH21 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ ((INT_MIN) <= ((Znth pos current_dist 0) - 1 )) ”
.

Definition solve_safety_wit_47 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best <> 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH14 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH15 : ((Zlength (latest)) = n_pre)) (PreH16 : ((Zlength (counts)) = n_pre)) (PreH17 : ((Zlength (arrivals)) = n_pre)) (PreH18 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH19 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH20 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH21 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_48 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best <> 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH14 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH15 : ((Zlength (latest)) = n_pre)) (PreH16 : ((Zlength (counts)) = n_pre)) (PreH17 : ((Zlength (arrivals)) = n_pre)) (PreH18 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH19 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH20 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH21 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) (replace_Znth (pos) (((Znth pos current_dist 0) - 1 )) (current_dist)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ ((pos + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pos + 1 )) ”
.

Definition solve_safety_wit_49 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best <> 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH14 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH15 : ((Zlength (latest)) = n_pre)) (PreH16 : ((Zlength (counts)) = n_pre)) (PreH17 : ((Zlength (arrivals)) = n_pre)) (PreH18 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH19 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH20 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH21 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) (replace_Znth (pos) (((Znth pos current_dist 0) - 1 )) (current_dist)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_50 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (new_arrivals: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (old_dist: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= pos)) (PreH6 : (pos < (n_pre - 1 ))) (PreH7 : (0 < best)) (PreH8 : (best <= m_pre)) (PreH9 : ((pos + 1 ) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH12 : ((Zlength (old_dist)) = (n_pre - 1 ))) (PreH13 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (old_arrivals)) = n_pre)) (PreH15 : ((Zlength (new_arrivals)) = n_pre)) (PreH16 : ((Zlength (latest)) = n_pre)) (PreH17 : ((Zlength (counts)) = n_pre)) (PreH18 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (new_dist) (0))) /\ ((Znth (edge) (new_dist) (0)) <= 100)))) (PreH19 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (new_arrivals) (0)))) /\ ((Znth (station) (new_arrivals) (0)) <= 200000)))) (PreH20 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals )) (PreH21 : (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos )) (PreH22 : (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos i )) ,
  (IntArray.full arr_pre n_pre new_arrivals )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) new_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ (((Znth i new_arrivals 0) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i new_arrivals 0) - 1 )) ”
) \/
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (new_arrivals: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (old_dist: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= pos)) (PreH6 : (pos < (n_pre - 1 ))) (PreH7 : (0 < best)) (PreH8 : (best <= m_pre)) (PreH9 : ((pos + 1 ) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH12 : ((Zlength (old_dist)) = (n_pre - 1 ))) (PreH13 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (old_arrivals)) = n_pre)) (PreH15 : ((Zlength (new_arrivals)) = n_pre)) (PreH16 : ((Zlength (latest)) = n_pre)) (PreH17 : ((Zlength (counts)) = n_pre)) (PreH18 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (new_dist) (0))) /\ ((Znth (edge) (new_dist) (0)) <= 100)))) (PreH19 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (new_arrivals) (0)))) /\ ((Znth (station) (new_arrivals) (0)) <= 200000)))) (PreH20 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals )) (PreH21 : (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos )) (PreH22 : (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos i )) ,
  (IntArray.full arr_pre n_pre new_arrivals )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) new_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ (((Znth i new_arrivals 0) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i new_arrivals 0) - 1 )) ”
).

Definition solve_safety_wit_50_split_goal_1 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (new_arrivals: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (old_dist: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= pos)) (PreH6 : (pos < (n_pre - 1 ))) (PreH7 : (0 < best)) (PreH8 : (best <= m_pre)) (PreH9 : ((pos + 1 ) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH12 : ((Zlength (old_dist)) = (n_pre - 1 ))) (PreH13 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (old_arrivals)) = n_pre)) (PreH15 : ((Zlength (new_arrivals)) = n_pre)) (PreH16 : ((Zlength (latest)) = n_pre)) (PreH17 : ((Zlength (counts)) = n_pre)) (PreH18 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (new_dist) (0))) /\ ((Znth (edge) (new_dist) (0)) <= 100)))) (PreH19 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (new_arrivals) (0)))) /\ ((Znth (station) (new_arrivals) (0)) <= 200000)))) (PreH20 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals )) (PreH21 : (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos )) (PreH22 : (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos i )) ,
  (IntArray.full arr_pre n_pre new_arrivals )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) new_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ (((Znth i new_arrivals 0) - 1 ) <= INT_MAX) ”
.

Definition solve_safety_wit_50_split_goal_2 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (new_arrivals: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (old_dist: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= pos)) (PreH6 : (pos < (n_pre - 1 ))) (PreH7 : (0 < best)) (PreH8 : (best <= m_pre)) (PreH9 : ((pos + 1 ) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH12 : ((Zlength (old_dist)) = (n_pre - 1 ))) (PreH13 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (old_arrivals)) = n_pre)) (PreH15 : ((Zlength (new_arrivals)) = n_pre)) (PreH16 : ((Zlength (latest)) = n_pre)) (PreH17 : ((Zlength (counts)) = n_pre)) (PreH18 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (new_dist) (0))) /\ ((Znth (edge) (new_dist) (0)) <= 100)))) (PreH19 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (new_arrivals) (0)))) /\ ((Znth (station) (new_arrivals) (0)) <= 200000)))) (PreH20 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals )) (PreH21 : (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos )) (PreH22 : (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos i )) ,
  (IntArray.full arr_pre n_pre new_arrivals )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) new_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ ((INT_MIN) <= ((Znth i new_arrivals 0) - 1 )) ”
.

Definition solve_safety_wit_51 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (new_arrivals: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (old_dist: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= pos)) (PreH6 : (pos < (n_pre - 1 ))) (PreH7 : (0 < best)) (PreH8 : (best <= m_pre)) (PreH9 : ((pos + 1 ) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH12 : ((Zlength (old_dist)) = (n_pre - 1 ))) (PreH13 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (old_arrivals)) = n_pre)) (PreH15 : ((Zlength (new_arrivals)) = n_pre)) (PreH16 : ((Zlength (latest)) = n_pre)) (PreH17 : ((Zlength (counts)) = n_pre)) (PreH18 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (new_dist) (0))) /\ ((Znth (edge) (new_dist) (0)) <= 100)))) (PreH19 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (new_arrivals) (0)))) /\ ((Znth (station) (new_arrivals) (0)) <= 200000)))) (PreH20 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals )) (PreH21 : (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos )) (PreH22 : (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos i )) ,
  (IntArray.full arr_pre n_pre new_arrivals )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) new_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_52 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (new_arrivals: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (old_dist: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : ((Znth i (replace_Znth (i) (((Znth i new_arrivals 0) - 1 )) (new_arrivals)) 0) >= (Znth i latest 0))) (PreH2 : (i < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= pos)) (PreH7 : (pos < (n_pre - 1 ))) (PreH8 : (0 < best)) (PreH9 : (best <= m_pre)) (PreH10 : ((pos + 1 ) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : ((Zlength (old_dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH15 : ((Zlength (old_arrivals)) = n_pre)) (PreH16 : ((Zlength (new_arrivals)) = n_pre)) (PreH17 : ((Zlength (latest)) = n_pre)) (PreH18 : ((Zlength (counts)) = n_pre)) (PreH19 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (new_dist) (0))) /\ ((Znth (edge) (new_dist) (0)) <= 100)))) (PreH20 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (new_arrivals) (0)))) /\ ((Znth (station) (new_arrivals) (0)) <= 200000)))) (PreH21 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals )) (PreH22 : (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos )) (PreH23 : (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos i )) ,
  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full arr_pre n_pre (replace_Znth (i) (((Znth i new_arrivals 0) - 1 )) (new_arrivals)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) new_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_53 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (old_dist: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (new_arrivals: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (k: Z) (pos: Z) (best: Z) (i: Z) (PreH1 : (0 < k)) (PreH2 : (k <= k_pre)) (PreH3 : (k_pre <= 100000)) (PreH4 : (0 <= pos)) (PreH5 : (pos < (n_pre - 1 ))) (PreH6 : (0 < best)) (PreH7 : (best <= m_pre)) (PreH8 : ((pos + 1 ) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH11 : ((Zlength (new_arrivals)) = n_pre)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals )) (PreH14 : (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos )) (PreH15 : (SelectedExchangeCertificate n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals best )) (PreH16 : (ArrivalRepairOutcome n_pre old_dist old_arrivals new_dist new_arrivals latest pos )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) new_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre new_arrivals )
|--
  “ ((k - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - 1 )) ”
.

Definition solve_safety_wit_54 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (old_dist: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (new_arrivals: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (k: Z) (pos: Z) (best: Z) (i: Z) (PreH1 : (0 < k)) (PreH2 : (k <= k_pre)) (PreH3 : (k_pre <= 100000)) (PreH4 : (0 <= pos)) (PreH5 : (pos < (n_pre - 1 ))) (PreH6 : (0 < best)) (PreH7 : (best <= m_pre)) (PreH8 : ((pos + 1 ) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH11 : ((Zlength (new_arrivals)) = n_pre)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals )) (PreH14 : (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos )) (PreH15 : (SelectedExchangeCertificate n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals best )) (PreH16 : (ArrivalRepairOutcome n_pre old_dist old_arrivals new_dist new_arrivals latest pos )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) new_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre new_arrivals )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_55 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (k: Z) (PreH1 : (k <= 0)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH6 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH7 : ((Zlength (latest)) = n_pre)) (PreH8 : ((Zlength (counts)) = n_pre)) (PreH9 : ((Zlength (arrivals)) = n_pre)) (PreH10 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH11 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH12 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_56 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (pos < 0)) (PreH2 : ((i + 1 ) >= n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (latest)) = n_pre)) (PreH15 : ((Zlength (counts)) = n_pre)) (PreH16 : ((Zlength (arrivals)) = n_pre)) (PreH17 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH18 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH19 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH20 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_57 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best = 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH14 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH15 : ((Zlength (latest)) = n_pre)) (PreH16 : ((Zlength (counts)) = n_pre)) (PreH17 : ((Zlength (arrivals)) = n_pre)) (PreH18 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH19 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH20 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH21 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_58 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (k: Z) (PreH1 : (k <= 0)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH6 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH7 : ((Zlength (latest)) = n_pre)) (PreH8 : ((Zlength (counts)) = n_pre)) (PreH9 : ((Zlength (arrivals)) = n_pre)) (PreH10 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH11 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH12 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |-> 0)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_59 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (pos < 0)) (PreH2 : ((i + 1 ) >= n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (latest)) = n_pre)) (PreH15 : ((Zlength (counts)) = n_pre)) (PreH16 : ((Zlength (arrivals)) = n_pre)) (PreH17 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH18 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH19 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH20 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |-> 0)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_60 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best = 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH14 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH15 : ((Zlength (latest)) = n_pre)) (PreH16 : ((Zlength (counts)) = n_pre)) (PreH17 : ((Zlength (arrivals)) = n_pre)) (PreH18 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH19 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH20 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH21 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |-> 0)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_61 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH21 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH22 : ((Zlength (arrivals)) = n_pre)) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals) (0))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH24 : forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))) (PreH25 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  (IntArray.full t_pre m_pre times )
  **  (IntArray.full arr_pre n_pre arrivals )
  **  (IntArray.full b_pre m_pre destinations )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ (((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals 0) ) - (Znth i times 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals 0) ) - (Znth i times 0) )) ”
) \/
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH21 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH22 : ((Zlength (arrivals)) = n_pre)) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals) (0))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH24 : forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))) (PreH25 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  (IntArray.full t_pre m_pre times )
  **  (IntArray.full arr_pre n_pre arrivals )
  **  (IntArray.full b_pre m_pre destinations )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ (((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals 0) ) - (Znth i times 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals 0) ) - (Znth i times 0) )) ”
).

Definition solve_safety_wit_61_split_goal_1 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH21 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH22 : ((Zlength (arrivals)) = n_pre)) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals) (0))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH24 : forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))) (PreH25 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  (IntArray.full t_pre m_pre times )
  **  (IntArray.full arr_pre n_pre arrivals )
  **  (IntArray.full b_pre m_pre destinations )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ (((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals 0) ) - (Znth i times 0) ) <= INT_MAX) ”
.

Definition solve_safety_wit_61_split_goal_2 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH21 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH22 : ((Zlength (arrivals)) = n_pre)) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals) (0))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH24 : forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))) (PreH25 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  (IntArray.full t_pre m_pre times )
  **  (IntArray.full arr_pre n_pre arrivals )
  **  (IntArray.full b_pre m_pre destinations )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ ((INT_MIN) <= ((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals 0) ) - (Znth i times 0) )) ”
.

Definition solve_safety_wit_62 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH21 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH22 : ((Zlength (arrivals)) = n_pre)) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals) (0))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH24 : forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))) (PreH25 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  (IntArray.full arr_pre n_pre arrivals )
  **  (IntArray.full b_pre m_pre destinations )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ ((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ans + (Znth ((Znth i destinations 0) - 1 ) arrivals 0) )) ”
) \/
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH21 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH22 : ((Zlength (arrivals)) = n_pre)) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals) (0))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH24 : forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))) (PreH25 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  (IntArray.full arr_pre n_pre arrivals )
  **  (IntArray.full b_pre m_pre destinations )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ ((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ans + (Znth ((Znth i destinations 0) - 1 ) arrivals 0) )) ”
).

Definition solve_safety_wit_62_split_goal_1 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH21 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH22 : ((Zlength (arrivals)) = n_pre)) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals) (0))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH24 : forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))) (PreH25 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  (IntArray.full arr_pre n_pre arrivals )
  **  (IntArray.full b_pre m_pre destinations )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ ((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals 0) ) <= INT_MAX) ”
.

Definition solve_safety_wit_62_split_goal_2 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH21 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH22 : ((Zlength (arrivals)) = n_pre)) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals) (0))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH24 : forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))) (PreH25 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  (IntArray.full arr_pre n_pre arrivals )
  **  (IntArray.full b_pre m_pre destinations )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ ((INT_MIN) <= (ans + (Znth ((Znth i destinations 0) - 1 ) arrivals 0) )) ”
.

Definition solve_safety_wit_63 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH21 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH22 : ((Zlength (arrivals)) = n_pre)) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals) (0))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH24 : forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))) (PreH25 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  (IntArray.full b_pre m_pre destinations )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ (((Znth i destinations 0) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i destinations 0) - 1 )) ”
.

Definition solve_safety_wit_64 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH21 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH22 : ((Zlength (arrivals)) = n_pre)) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals) (0))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH24 : forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))) (PreH25 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  (IntArray.full b_pre m_pre destinations )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_65 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH21 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH22 : ((Zlength (arrivals)) = n_pre)) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals) (0))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH24 : forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))) (PreH25 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  (IntArray.full t_pre m_pre times )
  **  (IntArray.full arr_pre n_pre arrivals )
  **  (IntArray.full b_pre m_pre destinations )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "ans" ) )) # Int  |-> ((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals 0) ) - (Znth i times 0) ))
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_entail_wit_1 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (PreH1 : (0 <= k_pre)) (PreH2 : (k_pre <= 100000)) (PreH3 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) ,
  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.undef_full late_pre n_pre )
  **  (IntArray.undef_full off_pre n_pre )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  EX (counts_prefix: (@list Z))  (latest_prefix: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (latest_prefix)) = 0) ” 
  &&  “ ((Zlength (counts_prefix)) = 0) ” 
  &&  “ (WorkspacesZeroPrefix latest_prefix counts_prefix 0 ) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.seg late_pre 0 0 latest_prefix )
  **  (IntArray.undef_seg late_pre 0 n_pre )
  **  (IntArray.seg off_pre 0 0 counts_prefix )
  **  (IntArray.undef_seg off_pre 0 n_pre )
  **  (IntArray.undef_full arr_pre n_pre )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (PreH1 : (0 <= k_pre)) (PreH2 : (k_pre <= 100000)) (PreH3 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) ,
  TT && emp 
|--
  “ (WorkspacesZeroPrefix (@nil Z) (@nil Z) 0 ) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ (0 <= n_pre) ”
  &&  emp
).

Definition solve_entail_wit_1_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (PreH1 : (0 <= k_pre)) (PreH2 : (k_pre <= 100000)) (PreH3 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) ,
  (WorkspacesZeroPrefix (@nil Z) (@nil Z) 0 )
.

Definition solve_entail_wit_1_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (PreH1 : (0 <= k_pre)) (PreH2 : (k_pre <= 100000)) (PreH3 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition solve_entail_wit_1_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (PreH1 : (0 <= k_pre)) (PreH2 : (k_pre <= 100000)) (PreH3 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition solve_entail_wit_1_split_goal_4 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (PreH1 : (0 <= k_pre)) (PreH2 : (k_pre <= 100000)) (PreH3 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) ,
  (0 <= n_pre)
.

Definition solve_entail_wit_2 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_prefix_2: (@list Z)) (latest_prefix_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (latest_prefix_2)) = i)) (PreH5 : ((Zlength (counts_prefix_2)) = i)) (PreH6 : (WorkspacesZeroPrefix latest_prefix_2 counts_prefix_2 i )) (PreH7 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH8 : (0 <= k_pre)) (PreH9 : (k_pre <= 100000)) ,
  (IntArray.seg off_pre 0 (i + 1 ) (app (counts_prefix_2) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg off_pre (i + 1 ) n_pre )
  **  (IntArray.seg late_pre 0 (i + 1 ) (app (latest_prefix_2) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg late_pre (i + 1 ) n_pre )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  EX (counts_prefix: (@list Z))  (latest_prefix: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (latest_prefix)) = (i + 1 )) ” 
  &&  “ ((Zlength (counts_prefix)) = (i + 1 )) ” 
  &&  “ (WorkspacesZeroPrefix latest_prefix counts_prefix (i + 1 ) ) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.seg late_pre 0 (i + 1 ) latest_prefix )
  **  (IntArray.undef_seg late_pre (i + 1 ) n_pre )
  **  (IntArray.seg off_pre 0 (i + 1 ) counts_prefix )
  **  (IntArray.undef_seg off_pre (i + 1 ) n_pre )
  **  (IntArray.undef_full arr_pre n_pre )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_prefix_2: (@list Z)) (latest_prefix_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (latest_prefix_2)) = i)) (PreH5 : ((Zlength (counts_prefix_2)) = i)) (PreH6 : (WorkspacesZeroPrefix latest_prefix_2 counts_prefix_2 i )) (PreH7 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH8 : (0 <= k_pre)) (PreH9 : (k_pre <= 100000)) ,
  TT && emp 
|--
  “ (WorkspacesZeroPrefix (app (latest_prefix_2) ((cons (0) ((@nil Z))))) (app (counts_prefix_2) ((cons (0) ((@nil Z))))) (i + 1 ) ) ” 
  &&  “ ((Zlength ((app (counts_prefix_2) ((cons (0) ((@nil Z))))))) = (i + 1 )) ” 
  &&  “ ((Zlength ((app (latest_prefix_2) ((cons (0) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition solve_entail_wit_2_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_prefix_2: (@list Z)) (latest_prefix_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (latest_prefix_2)) = i)) (PreH5 : ((Zlength (counts_prefix_2)) = i)) (PreH6 : (WorkspacesZeroPrefix latest_prefix_2 counts_prefix_2 i )) (PreH7 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH8 : (0 <= k_pre)) (PreH9 : (k_pre <= 100000)) ,
  (WorkspacesZeroPrefix (app (latest_prefix_2) ((cons (0) ((@nil Z))))) (app (counts_prefix_2) ((cons (0) ((@nil Z))))) (i + 1 ) )
.

Definition solve_entail_wit_2_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_prefix_2: (@list Z)) (latest_prefix_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (latest_prefix_2)) = i)) (PreH5 : ((Zlength (counts_prefix_2)) = i)) (PreH6 : (WorkspacesZeroPrefix latest_prefix_2 counts_prefix_2 i )) (PreH7 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH8 : (0 <= k_pre)) (PreH9 : (k_pre <= 100000)) ,
  ((Zlength ((app (counts_prefix_2) ((cons (0) ((@nil Z))))))) = (i + 1 ))
.

Definition solve_entail_wit_2_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_prefix_2: (@list Z)) (latest_prefix_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (latest_prefix_2)) = i)) (PreH5 : ((Zlength (counts_prefix_2)) = i)) (PreH6 : (WorkspacesZeroPrefix latest_prefix_2 counts_prefix_2 i )) (PreH7 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH8 : (0 <= k_pre)) (PreH9 : (k_pre <= 100000)) ,
  ((Zlength ((app (latest_prefix_2) ((cons (0) ((@nil Z))))))) = (i + 1 ))
.

Definition solve_entail_wit_3 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_prefix: (@list Z)) (latest_prefix: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (latest_prefix)) = i)) (PreH5 : ((Zlength (counts_prefix)) = i)) (PreH6 : (WorkspacesZeroPrefix latest_prefix counts_prefix i )) (PreH7 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH8 : (0 <= k_pre)) (PreH9 : (k_pre <= 100000)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.seg late_pre 0 i latest_prefix )
  **  (IntArray.undef_seg late_pre i n_pre )
  **  (IntArray.seg off_pre 0 i counts_prefix )
  **  (IntArray.undef_seg off_pre i n_pre )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  EX (counts: (@list Z))  (latest: (@list Z)) ,
  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre))) ” 
  &&  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations 0 latest counts ) ”
  &&  ((( &( "i" ) )) # Int  |-> n_pre)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
) \/
(
forall (off_pre: Z) (late_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_prefix: (@list Z)) (latest_prefix: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (latest_prefix)) = i)) (PreH5 : ((Zlength (counts_prefix)) = i)) (PreH6 : (WorkspacesZeroPrefix latest_prefix counts_prefix i )) (PreH7 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH8 : (0 <= k_pre)) (PreH9 : (k_pre <= 100000)) ,
  (IntArray.seg late_pre 0 i latest_prefix )
  **  (IntArray.seg off_pre 0 i counts_prefix )
|--
  EX (counts: (@list Z))  (latest: (@list Z)) ,
  “ (i = n_pre) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre))) ” 
  &&  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations 0 latest counts ) ”
  &&  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
).

Definition solve_entail_wit_4 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (PreH1 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 100000)) (PreH4 : ((Zlength (latest_2)) = n_pre)) (PreH5 : ((Zlength (counts_2)) = n_pre)) (PreH6 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)))) (PreH7 : (PassengerAggregationPrefix n_pre m_pre times origins destinations 0 latest_2 counts_2 )) ,
  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest_2 )
  **  (IntArray.full off_pre n_pre counts_2 )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  EX (counts: (@list Z))  (latest: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= 0))) ” 
  &&  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations 0 latest counts ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (PreH1 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 100000)) (PreH4 : ((Zlength (latest_2)) = n_pre)) (PreH5 : ((Zlength (counts_2)) = n_pre)) (PreH6 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)))) (PreH7 : (PassengerAggregationPrefix n_pre m_pre times origins destinations 0 latest_2 counts_2 )) ,
  TT && emp 
|--
  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= 0))) ” 
  &&  “ (0 <= m_pre) ”
  &&  emp
).

Definition solve_entail_wit_4_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (PreH1 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 100000)) (PreH4 : ((Zlength (latest_2)) = n_pre)) (PreH5 : ((Zlength (counts_2)) = n_pre)) (PreH6 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)))) (PreH7 : (PassengerAggregationPrefix n_pre m_pre times origins destinations 0 latest_2 counts_2 )) ,
  forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= 0)))
.

Definition solve_entail_wit_4_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (PreH1 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 100000)) (PreH4 : ((Zlength (latest_2)) = n_pre)) (PreH5 : ((Zlength (counts_2)) = n_pre)) (PreH6 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)))) (PreH7 : (PassengerAggregationPrefix n_pre m_pre times origins destinations 0 latest_2 counts_2 )) ,
  (0 <= m_pre)
.

Definition solve_entail_wit_5 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : ((Zlength (latest)) = n_pre)) (PreH8 : ((Zlength (counts)) = n_pre)) (PreH9 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH10 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full b_pre m_pre destinations )
  **  ((( &( "y" ) )) # Int  |-> ((Znth i destinations 0) - 1 ))
  **  (IntArray.full a_pre m_pre origins )
  **  ((( &( "x" ) )) # Int  |-> ((Znth i origins 0) - 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ (0 <= ((Znth (i) (origins) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) < n_pre) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) = ((Znth (i) (origins) (0)) - 1 )) ” 
  &&  “ (k_pre <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (((Znth i destinations 0) - 1 ) <= INT_MAX) ” 
  &&  “ (k_pre >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (((Znth i destinations 0) - 1 ) >= INT_MIN) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i))) ” 
  &&  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts ) ”
  &&  ((( &( "x" ) )) # Int  |-> ((Znth (i) (origins) (0)) - 1 ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full b_pre m_pre destinations )
  **  ((( &( "y" ) )) # Int  |-> ((Znth i destinations 0) - 1 ))
  **  (IntArray.full a_pre m_pre origins )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (k_pre <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (((Znth i origins 0) - 1 ) <= INT_MAX)) (PreH6 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (k_pre >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (((Znth i origins 0) - 1 ) >= INT_MIN)) (PreH12 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH13 : (i < m_pre)) (PreH14 : (0 <= i)) (PreH15 : (i <= m_pre)) (PreH16 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH17 : (0 <= k_pre)) (PreH18 : (k_pre <= 100000)) (PreH19 : ((Zlength (latest)) = n_pre)) (PreH20 : ((Zlength (counts)) = n_pre)) (PreH21 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH22 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  TT && emp 
|--
  “ (((Znth (i) (origins) (0)) - 1 ) < n_pre) ” 
  &&  “ (0 <= ((Znth (i) (origins) (0)) - 1 )) ”
  &&  emp
).

Definition solve_entail_wit_5_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (k_pre <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (((Znth i origins 0) - 1 ) <= INT_MAX)) (PreH6 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (k_pre >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (((Znth i origins 0) - 1 ) >= INT_MIN)) (PreH12 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH13 : (i < m_pre)) (PreH14 : (0 <= i)) (PreH15 : (i <= m_pre)) (PreH16 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH17 : (0 <= k_pre)) (PreH18 : (k_pre <= 100000)) (PreH19 : ((Zlength (latest)) = n_pre)) (PreH20 : ((Zlength (counts)) = n_pre)) (PreH21 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH22 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (((Znth (i) (origins) (0)) - 1 ) < n_pre)
.

Definition solve_entail_wit_5_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (k_pre <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (((Znth i origins 0) - 1 ) <= INT_MAX)) (PreH6 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (k_pre >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (((Znth i origins 0) - 1 ) >= INT_MIN)) (PreH12 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH13 : (i < m_pre)) (PreH14 : (0 <= i)) (PreH15 : (i <= m_pre)) (PreH16 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH17 : (0 <= k_pre)) (PreH18 : (k_pre <= 100000)) (PreH19 : ((Zlength (latest)) = n_pre)) (PreH20 : ((Zlength (counts)) = n_pre)) (PreH21 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH22 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (0 <= ((Znth (i) (origins) (0)) - 1 ))
.

Definition solve_entail_wit_6 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH2 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) = ((Znth (i) (origins) (0)) - 1 ))) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH8 : (k_pre >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH12 : (i < m_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH16 : (0 <= k_pre)) (PreH17 : (k_pre <= 100000)) (PreH18 : ((Zlength (latest)) = n_pre)) (PreH19 : ((Zlength (counts)) = n_pre)) (PreH20 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH21 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  ((( &( "x" ) )) # Int  |-> ((Znth (i) (origins) (0)) - 1 ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full b_pre m_pre destinations )
  **  ((( &( "y" ) )) # Int  |-> ((Znth i destinations 0) - 1 ))
  **  (IntArray.full a_pre m_pre origins )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ (0 <= ((Znth (i) (destinations) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (destinations) (0)) - 1 ) < n_pre) ” 
  &&  “ (((Znth (i) (destinations) (0)) - 1 ) = ((Znth (i) (destinations) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN) ” 
  &&  “ (0 <= ((Znth (i) (origins) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) < n_pre) ” 
  &&  “ (k_pre <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (((Znth i destinations 0) - 1 ) <= INT_MAX) ” 
  &&  “ (k_pre >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (((Znth i destinations 0) - 1 ) >= INT_MIN) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i))) ” 
  &&  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts ) ”
  &&  ((( &( "y" ) )) # Int  |-> ((Znth (i) (destinations) (0)) - 1 ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> ((Znth (i) (origins) (0)) - 1 ))
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX)) (PreH3 : (i >= INT_MIN)) (PreH4 : (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN)) (PreH5 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH6 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH7 : (k_pre <= INT_MAX)) (PreH8 : (m_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH11 : (k_pre >= INT_MIN)) (PreH12 : (m_pre >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH15 : (i < m_pre)) (PreH16 : (0 <= i)) (PreH17 : (i <= m_pre)) (PreH18 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH19 : (0 <= k_pre)) (PreH20 : (k_pre <= 100000)) (PreH21 : ((Zlength (latest)) = n_pre)) (PreH22 : ((Zlength (counts)) = n_pre)) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH24 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  TT && emp 
|--
  “ (((Znth (i) (destinations) (0)) - 1 ) < n_pre) ” 
  &&  “ (0 <= ((Znth (i) (destinations) (0)) - 1 )) ”
  &&  emp
).

Definition solve_entail_wit_6_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX)) (PreH3 : (i >= INT_MIN)) (PreH4 : (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN)) (PreH5 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH6 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH7 : (k_pre <= INT_MAX)) (PreH8 : (m_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH11 : (k_pre >= INT_MIN)) (PreH12 : (m_pre >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH15 : (i < m_pre)) (PreH16 : (0 <= i)) (PreH17 : (i <= m_pre)) (PreH18 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH19 : (0 <= k_pre)) (PreH20 : (k_pre <= 100000)) (PreH21 : ((Zlength (latest)) = n_pre)) (PreH22 : ((Zlength (counts)) = n_pre)) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH24 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (((Znth (i) (destinations) (0)) - 1 ) < n_pre)
.

Definition solve_entail_wit_6_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX)) (PreH3 : (i >= INT_MIN)) (PreH4 : (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN)) (PreH5 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH6 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH7 : (k_pre <= INT_MAX)) (PreH8 : (m_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH11 : (k_pre >= INT_MIN)) (PreH12 : (m_pre >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH15 : (i < m_pre)) (PreH16 : (0 <= i)) (PreH17 : (i <= m_pre)) (PreH18 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH19 : (0 <= k_pre)) (PreH20 : (k_pre <= 100000)) (PreH21 : ((Zlength (latest)) = n_pre)) (PreH22 : ((Zlength (counts)) = n_pre)) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH24 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (0 <= ((Znth (i) (destinations) (0)) - 1 ))
.

Definition solve_entail_wit_7_1 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest_2 0) < (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH3 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH4 : (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX)) (PreH5 : (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN)) (PreH6 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH7 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH16 : (i < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= 100000)) (PreH22 : ((Zlength (latest_2)) = n_pre)) (PreH23 : ((Zlength (counts_2)) = n_pre)) (PreH24 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= i)))) (PreH25 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest_2 counts_2 )) ,
  (IntArray.full off_pre n_pre (replace_Znth (((Znth (i) (destinations) (0)) - 1 )) (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts_2 0) + 1 )) (counts_2)) )
  **  (IntArray.full late_pre n_pre (replace_Znth (((Znth (i) (origins) (0)) - 1 )) ((Znth i times 0)) (latest_2)) )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  EX (counts: (@list Z))  (latest: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= m_pre) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= (i + 1 )))) ” 
  &&  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations (i + 1 ) latest counts ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest_2 0) < (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH3 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH4 : (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX)) (PreH5 : (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN)) (PreH6 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH7 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH16 : (i < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= 100000)) (PreH22 : ((Zlength (latest_2)) = n_pre)) (PreH23 : ((Zlength (counts_2)) = n_pre)) (PreH24 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= i)))) (PreH25 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest_2 counts_2 )) ,
  TT && emp 
|--
  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations (i + 1 ) (replace_Znth (((Znth (i) (origins) (0)) - 1 )) ((Znth i times 0)) (latest_2)) (replace_Znth (((Znth (i) (destinations) (0)) - 1 )) (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts_2 0) + 1 )) (counts_2)) ) ” 
  &&  “ ((Zlength ((replace_Znth (((Znth (i) (destinations) (0)) - 1 )) (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts_2 0) + 1 )) (counts_2)))) = n_pre) ” 
  &&  “ ((Zlength ((replace_Znth (((Znth (i) (origins) (0)) - 1 )) ((Znth i times 0)) (latest_2)))) = n_pre) ”
  &&  emp
).

Definition solve_entail_wit_7_1_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest_2 0) < (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH3 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH4 : (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX)) (PreH5 : (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN)) (PreH6 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH7 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH16 : (i < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= 100000)) (PreH22 : ((Zlength (latest_2)) = n_pre)) (PreH23 : ((Zlength (counts_2)) = n_pre)) (PreH24 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= i)))) (PreH25 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest_2 counts_2 )) ,
  (PassengerAggregationPrefix n_pre m_pre times origins destinations (i + 1 ) (replace_Znth (((Znth (i) (origins) (0)) - 1 )) ((Znth i times 0)) (latest_2)) (replace_Znth (((Znth (i) (destinations) (0)) - 1 )) (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts_2 0) + 1 )) (counts_2)) )
.

Definition solve_entail_wit_7_1_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest_2 0) < (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH3 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH4 : (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX)) (PreH5 : (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN)) (PreH6 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH7 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH16 : (i < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= 100000)) (PreH22 : ((Zlength (latest_2)) = n_pre)) (PreH23 : ((Zlength (counts_2)) = n_pre)) (PreH24 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= i)))) (PreH25 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest_2 counts_2 )) ,
  ((Zlength ((replace_Znth (((Znth (i) (destinations) (0)) - 1 )) (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts_2 0) + 1 )) (counts_2)))) = n_pre)
.

Definition solve_entail_wit_7_1_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest_2 0) < (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH3 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH4 : (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX)) (PreH5 : (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN)) (PreH6 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH7 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH16 : (i < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= 100000)) (PreH22 : ((Zlength (latest_2)) = n_pre)) (PreH23 : ((Zlength (counts_2)) = n_pre)) (PreH24 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= i)))) (PreH25 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest_2 counts_2 )) ,
  ((Zlength ((replace_Znth (((Znth (i) (origins) (0)) - 1 )) ((Znth i times 0)) (latest_2)))) = n_pre)
.

Definition solve_entail_wit_7_2 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest_2 0) >= (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH3 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH4 : (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX)) (PreH5 : (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN)) (PreH6 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH7 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH16 : (i < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= 100000)) (PreH22 : ((Zlength (latest_2)) = n_pre)) (PreH23 : ((Zlength (counts_2)) = n_pre)) (PreH24 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= i)))) (PreH25 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest_2 counts_2 )) ,
  (IntArray.full off_pre n_pre (replace_Znth (((Znth (i) (destinations) (0)) - 1 )) (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts_2 0) + 1 )) (counts_2)) )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full late_pre n_pre latest_2 )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  EX (counts: (@list Z))  (latest: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= m_pre) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= (i + 1 )))) ” 
  &&  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations (i + 1 ) latest counts ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest_2 0) >= (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH3 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH4 : (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX)) (PreH5 : (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN)) (PreH6 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH7 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH16 : (i < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= 100000)) (PreH22 : ((Zlength (latest_2)) = n_pre)) (PreH23 : ((Zlength (counts_2)) = n_pre)) (PreH24 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= i)))) (PreH25 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest_2 counts_2 )) ,
  TT && emp 
|--
  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations (i + 1 ) latest_2 (replace_Znth (((Znth (i) (destinations) (0)) - 1 )) (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts_2 0) + 1 )) (counts_2)) ) ” 
  &&  “ ((Zlength ((replace_Znth (((Znth (i) (destinations) (0)) - 1 )) (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts_2 0) + 1 )) (counts_2)))) = n_pre) ”
  &&  emp
).

Definition solve_entail_wit_7_2_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest_2 0) >= (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH3 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH4 : (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX)) (PreH5 : (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN)) (PreH6 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH7 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH16 : (i < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= 100000)) (PreH22 : ((Zlength (latest_2)) = n_pre)) (PreH23 : ((Zlength (counts_2)) = n_pre)) (PreH24 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= i)))) (PreH25 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest_2 counts_2 )) ,
  (PassengerAggregationPrefix n_pre m_pre times origins destinations (i + 1 ) latest_2 (replace_Znth (((Znth (i) (destinations) (0)) - 1 )) (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts_2 0) + 1 )) (counts_2)) )
.

Definition solve_entail_wit_7_2_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest_2 0) >= (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH3 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH4 : (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX)) (PreH5 : (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN)) (PreH6 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH7 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH16 : (i < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= 100000)) (PreH22 : ((Zlength (latest_2)) = n_pre)) (PreH23 : ((Zlength (counts_2)) = n_pre)) (PreH24 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= i)))) (PreH25 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest_2 counts_2 )) ,
  ((Zlength ((replace_Znth (((Znth (i) (destinations) (0)) - 1 )) (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts_2 0) + 1 )) (counts_2)))) = n_pre)
.

Definition solve_entail_wit_8 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : ((Zlength (latest_2)) = n_pre)) (PreH8 : ((Zlength (counts_2)) = n_pre)) (PreH9 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= i)))) (PreH10 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest_2 counts_2 )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest_2 )
  **  (IntArray.full off_pre n_pre counts_2 )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  EX (latest: (@list Z))  (counts: (@list Z)) ,
  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (StationSummaryState n_pre m_pre times origins destinations latest counts ) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre))) ”
  &&  ((( &( "i" ) )) # Int  |-> m_pre)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : ((Zlength (latest_2)) = n_pre)) (PreH8 : ((Zlength (counts_2)) = n_pre)) (PreH9 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= i)))) (PreH10 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest_2 counts_2 )) ,
  TT && emp 
|--
  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre))) ” 
  &&  “ (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 ) ”
  &&  emp
).

Definition solve_entail_wit_8_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : ((Zlength (latest_2)) = n_pre)) (PreH8 : ((Zlength (counts_2)) = n_pre)) (PreH9 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= i)))) (PreH10 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest_2 counts_2 )) ,
  forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)))
.

Definition solve_entail_wit_8_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : ((Zlength (latest_2)) = n_pre)) (PreH8 : ((Zlength (counts_2)) = n_pre)) (PreH9 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= i)))) (PreH10 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest_2 counts_2 )) ,
  (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )
.

Definition solve_entail_wit_9 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (PreH1 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 100000)) (PreH4 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH5 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)))) ,
  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest_2 )
  **  (IntArray.full off_pre n_pre counts_2 )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  EX (latest: (@list Z))  (counts: (@list Z))  (arrivals_prefix: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 200000) ” 
  &&  “ ((Zlength (arrivals_prefix)) = 0) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (StationSummaryState n_pre m_pre times origins destinations latest counts ) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre))) ” 
  &&  “ (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix 0 0 ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.seg arr_pre 0 0 arrivals_prefix )
  **  (IntArray.undef_seg arr_pre 0 n_pre )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (PreH1 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 100000)) (PreH4 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH5 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)))) ,
  TT && emp 
|--
  “ (ArrivalSimulationPrefix n_pre dist latest_2 (@nil Z) 0 0 ) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre))) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ (0 <= n_pre) ”
  &&  emp
).

Definition solve_entail_wit_9_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (PreH1 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 100000)) (PreH4 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH5 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)))) ,
  (ArrivalSimulationPrefix n_pre dist latest_2 (@nil Z) 0 0 )
.

Definition solve_entail_wit_9_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (PreH1 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 100000)) (PreH4 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH5 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)))) ,
  forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)))
.

Definition solve_entail_wit_9_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (PreH1 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 100000)) (PreH4 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH5 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)))) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition solve_entail_wit_9_split_goal_4 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (PreH1 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH2 : (0 <= k_pre)) (PreH3 : (k_pre <= 100000)) (PreH4 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH5 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)))) ,
  (0 <= n_pre)
.

Definition solve_entail_wit_10_1 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur < (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= 100000)) (PreH12 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)))) (PreH14 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full late_pre n_pre latest_2 )
  **  (IntArray.seg arr_pre 0 (i + 1 ) (app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg arr_pre (i + 1 ) n_pre )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full off_pre n_pre counts_2 )
|--
  EX (latest: (@list Z))  (counts: (@list Z))  (arrivals_prefix: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= ((Znth i latest_2 0) + (Znth i dist 0) )) ” 
  &&  “ (((Znth i latest_2 0) + (Znth i dist 0) ) <= 200000) ” 
  &&  “ ((Zlength (arrivals_prefix)) = (i + 1 )) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (StationSummaryState n_pre m_pre times origins destinations latest counts ) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre))) ” 
  &&  “ (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix (i + 1 ) ((Znth i latest_2 0) + (Znth i dist 0) ) ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.seg arr_pre 0 (i + 1 ) arrivals_prefix )
  **  (IntArray.undef_seg arr_pre (i + 1 ) n_pre )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur < (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= 100000)) (PreH12 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)))) (PreH14 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  TT && emp 
|--
  “ (ArrivalSimulationPrefix n_pre dist latest_2 (app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))) (i + 1 ) ((Znth i latest_2 0) + (Znth i dist 0) ) ) ” 
  &&  “ ((Zlength ((app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))))) = (i + 1 )) ” 
  &&  “ (((Znth i latest_2 0) + (Znth i dist 0) ) <= 200000) ” 
  &&  “ (0 <= ((Znth i latest_2 0) + (Znth i dist 0) )) ”
  &&  emp
).

Definition solve_entail_wit_10_1_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur < (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= 100000)) (PreH12 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)))) (PreH14 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  (ArrivalSimulationPrefix n_pre dist latest_2 (app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))) (i + 1 ) ((Znth i latest_2 0) + (Znth i dist 0) ) )
.

Definition solve_entail_wit_10_1_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur < (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= 100000)) (PreH12 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)))) (PreH14 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  ((Zlength ((app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))))) = (i + 1 ))
.

Definition solve_entail_wit_10_1_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur < (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= 100000)) (PreH12 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)))) (PreH14 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  (((Znth i latest_2 0) + (Znth i dist 0) ) <= 200000)
.

Definition solve_entail_wit_10_1_split_goal_4 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur < (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= 100000)) (PreH12 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)))) (PreH14 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  (0 <= ((Znth i latest_2 0) + (Znth i dist 0) ))
.

Definition solve_entail_wit_10_2 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur >= (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= 100000)) (PreH12 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)))) (PreH14 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full late_pre n_pre latest_2 )
  **  (IntArray.seg arr_pre 0 (i + 1 ) (app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg arr_pre (i + 1 ) n_pre )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full off_pre n_pre counts_2 )
|--
  EX (latest: (@list Z))  (counts: (@list Z))  (arrivals_prefix: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (cur + (Znth i dist 0) )) ” 
  &&  “ ((cur + (Znth i dist 0) ) <= 200000) ” 
  &&  “ ((Zlength (arrivals_prefix)) = (i + 1 )) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (StationSummaryState n_pre m_pre times origins destinations latest counts ) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre))) ” 
  &&  “ (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix (i + 1 ) (cur + (Znth i dist 0) ) ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.seg arr_pre 0 (i + 1 ) arrivals_prefix )
  **  (IntArray.undef_seg arr_pre (i + 1 ) n_pre )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur >= (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= 100000)) (PreH12 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)))) (PreH14 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  TT && emp 
|--
  “ (ArrivalSimulationPrefix n_pre dist latest_2 (app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))) (i + 1 ) (cur + (Znth i dist 0) ) ) ” 
  &&  “ ((Zlength ((app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))))) = (i + 1 )) ” 
  &&  “ ((cur + (Znth i dist 0) ) <= 200000) ” 
  &&  “ (0 <= (cur + (Znth i dist 0) )) ”
  &&  emp
).

Definition solve_entail_wit_10_2_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur >= (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= 100000)) (PreH12 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)))) (PreH14 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  (ArrivalSimulationPrefix n_pre dist latest_2 (app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))) (i + 1 ) (cur + (Znth i dist 0) ) )
.

Definition solve_entail_wit_10_2_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur >= (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= 100000)) (PreH12 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)))) (PreH14 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  ((Zlength ((app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))))) = (i + 1 ))
.

Definition solve_entail_wit_10_2_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur >= (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= 100000)) (PreH12 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)))) (PreH14 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  ((cur + (Znth i dist 0) ) <= 200000)
.

Definition solve_entail_wit_10_2_split_goal_4 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur >= (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= 100000)) (PreH12 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)))) (PreH14 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  (0 <= (cur + (Znth i dist 0) ))
.

Definition solve_entail_wit_10_3 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (cur < (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= 100000)) (PreH12 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)))) (PreH14 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  (IntArray.full late_pre n_pre latest_2 )
  **  (IntArray.seg arr_pre 0 (i + 1 ) (app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg arr_pre (i + 1 ) n_pre )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full off_pre n_pre counts_2 )
|--
  EX (latest: (@list Z))  (counts: (@list Z))  (arrivals_prefix: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (Znth i latest_2 0)) ” 
  &&  “ ((Znth i latest_2 0) <= 200000) ” 
  &&  “ ((Zlength (arrivals_prefix)) = (i + 1 )) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (StationSummaryState n_pre m_pre times origins destinations latest counts ) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre))) ” 
  &&  “ (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix (i + 1 ) (Znth i latest_2 0) ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.seg arr_pre 0 (i + 1 ) arrivals_prefix )
  **  (IntArray.undef_seg arr_pre (i + 1 ) n_pre )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (cur < (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= 100000)) (PreH12 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)))) (PreH14 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  TT && emp 
|--
  “ (ArrivalSimulationPrefix n_pre dist latest_2 (app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))) (i + 1 ) (Znth i latest_2 0) ) ” 
  &&  “ ((Zlength ((app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))))) = (i + 1 )) ” 
  &&  “ ((Znth i latest_2 0) <= 200000) ”
  &&  emp
).

Definition solve_entail_wit_10_3_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (cur < (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= 100000)) (PreH12 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)))) (PreH14 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  (ArrivalSimulationPrefix n_pre dist latest_2 (app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))) (i + 1 ) (Znth i latest_2 0) )
.

Definition solve_entail_wit_10_3_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (cur < (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= 100000)) (PreH12 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)))) (PreH14 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  ((Zlength ((app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))))) = (i + 1 ))
.

Definition solve_entail_wit_10_3_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (cur < (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= 100000)) (PreH12 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)))) (PreH14 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  ((Znth i latest_2 0) <= 200000)
.

Definition solve_entail_wit_10_4 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (cur >= (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= 100000)) (PreH12 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)))) (PreH14 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  (IntArray.full late_pre n_pre latest_2 )
  **  (IntArray.seg arr_pre 0 (i + 1 ) (app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg arr_pre (i + 1 ) n_pre )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full off_pre n_pre counts_2 )
|--
  EX (latest: (@list Z))  (counts: (@list Z))  (arrivals_prefix: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= 200000) ” 
  &&  “ ((Zlength (arrivals_prefix)) = (i + 1 )) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (StationSummaryState n_pre m_pre times origins destinations latest counts ) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre))) ” 
  &&  “ (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix (i + 1 ) cur ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.seg arr_pre 0 (i + 1 ) arrivals_prefix )
  **  (IntArray.undef_seg arr_pre (i + 1 ) n_pre )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (cur >= (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= 100000)) (PreH12 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)))) (PreH14 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  TT && emp 
|--
  “ (ArrivalSimulationPrefix n_pre dist latest_2 (app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))) (i + 1 ) cur ) ” 
  &&  “ ((Zlength ((app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition solve_entail_wit_10_4_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (cur >= (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= 100000)) (PreH12 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)))) (PreH14 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  (ArrivalSimulationPrefix n_pre dist latest_2 (app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))) (i + 1 ) cur )
.

Definition solve_entail_wit_10_4_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (cur >= (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= 100000)) (PreH12 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)))) (PreH14 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  ((Zlength ((app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))))) = (i + 1 ))
.

Definition solve_entail_wit_11 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= cur)) (PreH5 : (cur <= 200000)) (PreH6 : ((Zlength (arrivals_prefix)) = i)) (PreH7 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH8 : (0 <= k_pre)) (PreH9 : (k_pre <= 100000)) (PreH10 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH11 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)))) (PreH12 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix i cur )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest_2 )
  **  (IntArray.full off_pre n_pre counts_2 )
  **  (IntArray.seg arr_pre 0 i arrivals_prefix )
  **  (IntArray.undef_seg arr_pre i n_pre )
|--
  EX (latest: (@list Z))  (counts: (@list Z))  (arrivals: (@list Z)) ,
  “ (0 <= cur) ” 
  &&  “ (cur <= 200000) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (CanonicalBusState n_pre m_pre times origins destinations dist latest counts arrivals ) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals) (0))) /\ ((Znth (station) (arrivals) (0)) <= 200000))) ”
  &&  ((( &( "i" ) )) # Int  |-> n_pre)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
) \/
(
forall (arr_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= cur)) (PreH5 : (cur <= 200000)) (PreH6 : ((Zlength (arrivals_prefix)) = i)) (PreH7 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH8 : (0 <= k_pre)) (PreH9 : (k_pre <= 100000)) (PreH10 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH11 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)))) (PreH12 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix i cur )) ,
  (IntArray.seg arr_pre 0 i arrivals_prefix )
|--
  EX (arrivals: (@list Z)) ,
  “ (i = n_pre) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= 200000) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (CanonicalBusState n_pre m_pre times origins destinations dist latest_2 counts_2 arrivals ) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals) (0))) /\ ((Znth (station) (arrivals) (0)) <= 200000))) ”
  &&  (IntArray.full arr_pre n_pre arrivals )
).

Definition solve_entail_wit_12 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (cur: Z) (PreH1 : (0 <= cur)) (PreH2 : (cur <= 200000)) (PreH3 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH4 : (0 <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (CanonicalBusState n_pre m_pre times origins destinations dist latest_2 counts_2 arrivals_2 )) (PreH7 : ((Zlength (arrivals_2)) = n_pre)) (PreH8 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((0 <= (Znth (station_2) (arrivals_2) (0))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) ,
  ((( &( "i" ) )) # Int  |-> n_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest_2 )
  **  (IntArray.full off_pre n_pre counts_2 )
  **  (IntArray.full arr_pre n_pre arrivals_2 )
|--
  EX (arrivals: (@list Z))  (counts: (@list Z))  (latest: (@list Z))  (current_dist: (@list Z)) ,
  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ ((Zlength (current_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100))) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000))) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k_pre dist times origins destinations current_dist latest counts arrivals ) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (cur: Z) (PreH1 : (0 <= cur)) (PreH2 : (cur <= 200000)) (PreH3 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH4 : (0 <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (CanonicalBusState n_pre m_pre times origins destinations dist latest_2 counts_2 arrivals_2 )) (PreH7 : ((Zlength (arrivals_2)) = n_pre)) (PreH8 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((0 <= (Znth (station_2) (arrivals_2) (0))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) ,
  TT && emp 
|--
  “ (BoosterProgress n_pre m_pre k_pre k_pre dist times origins destinations dist latest_2 counts_2 arrivals_2 ) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals_2) (0)))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000))) ” 
  &&  “ forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (dist) (0))) /\ ((Znth (edge) (dist) (0)) <= 100))) ” 
  &&  “ ((Zlength (counts_2)) = n_pre) ” 
  &&  “ ((Zlength (latest_2)) = n_pre) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ”
  &&  emp
).

Definition solve_entail_wit_12_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (cur: Z) (PreH1 : (0 <= cur)) (PreH2 : (cur <= 200000)) (PreH3 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH4 : (0 <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (CanonicalBusState n_pre m_pre times origins destinations dist latest_2 counts_2 arrivals_2 )) (PreH7 : ((Zlength (arrivals_2)) = n_pre)) (PreH8 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((0 <= (Znth (station_2) (arrivals_2) (0))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) ,
  (BoosterProgress n_pre m_pre k_pre k_pre dist times origins destinations dist latest_2 counts_2 arrivals_2 )
.

Definition solve_entail_wit_12_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (cur: Z) (PreH1 : (0 <= cur)) (PreH2 : (cur <= 200000)) (PreH3 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH4 : (0 <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (CanonicalBusState n_pre m_pre times origins destinations dist latest_2 counts_2 arrivals_2 )) (PreH7 : ((Zlength (arrivals_2)) = n_pre)) (PreH8 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((0 <= (Znth (station_2) (arrivals_2) (0))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) ,
  forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals_2) (0)))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))
.

Definition solve_entail_wit_12_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (cur: Z) (PreH1 : (0 <= cur)) (PreH2 : (cur <= 200000)) (PreH3 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH4 : (0 <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (CanonicalBusState n_pre m_pre times origins destinations dist latest_2 counts_2 arrivals_2 )) (PreH7 : ((Zlength (arrivals_2)) = n_pre)) (PreH8 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((0 <= (Znth (station_2) (arrivals_2) (0))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) ,
  forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (dist) (0))) /\ ((Znth (edge) (dist) (0)) <= 100)))
.

Definition solve_entail_wit_12_split_goal_4 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (cur: Z) (PreH1 : (0 <= cur)) (PreH2 : (cur <= 200000)) (PreH3 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH4 : (0 <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (CanonicalBusState n_pre m_pre times origins destinations dist latest_2 counts_2 arrivals_2 )) (PreH7 : ((Zlength (arrivals_2)) = n_pre)) (PreH8 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((0 <= (Znth (station_2) (arrivals_2) (0))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) ,
  ((Zlength (counts_2)) = n_pre)
.

Definition solve_entail_wit_12_split_goal_5 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (cur: Z) (PreH1 : (0 <= cur)) (PreH2 : (cur <= 200000)) (PreH3 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH4 : (0 <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (CanonicalBusState n_pre m_pre times origins destinations dist latest_2 counts_2 arrivals_2 )) (PreH7 : ((Zlength (arrivals_2)) = n_pre)) (PreH8 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((0 <= (Znth (station_2) (arrivals_2) (0))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) ,
  ((Zlength (latest_2)) = n_pre)
.

Definition solve_entail_wit_12_split_goal_6 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (cur: Z) (PreH1 : (0 <= cur)) (PreH2 : (cur <= 200000)) (PreH3 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH4 : (0 <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (CanonicalBusState n_pre m_pre times origins destinations dist latest_2 counts_2 arrivals_2 )) (PreH7 : ((Zlength (arrivals_2)) = n_pre)) (PreH8 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((0 <= (Znth (station_2) (arrivals_2) (0))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) ,
  ((Zlength (dist)) = (n_pre - 1 ))
.

Definition solve_entail_wit_13 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (k: Z) (PreH1 : (k > 0)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH6 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH7 : ((Zlength (latest_2)) = n_pre)) (PreH8 : ((Zlength (counts_2)) = n_pre)) (PreH9 : ((Zlength (arrivals_2)) = n_pre)) (PreH10 : forall (edge_2: Z) , (((0 <= edge_2) /\ (edge_2 < (n_pre - 1 ))) -> ((0 <= (Znth (edge_2) (current_dist_2) (0))) /\ ((Znth (edge_2) (current_dist_2) (0)) <= 100)))) (PreH11 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station_2) (arrivals_2) (0)))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) (PreH12 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist_2 )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest_2 )
  **  (IntArray.full off_pre n_pre counts_2 )
  **  (IntArray.full arr_pre n_pre arrivals_2 )
|--
  EX (arrivals: (@list Z))  (counts: (@list Z))  (latest: (@list Z))  (current_dist: (@list Z)) ,
  “ (0 < k) ” 
  &&  “ (k <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre - 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) < 0) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ ((Zlength (current_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100))) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000))) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals ) ” 
  &&  “ (EdgeChoicePrefix n_pre current_dist counts latest arrivals 0 0 (-1) ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (k: Z) (PreH1 : (k > 0)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH6 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH7 : ((Zlength (latest_2)) = n_pre)) (PreH8 : ((Zlength (counts_2)) = n_pre)) (PreH9 : ((Zlength (arrivals_2)) = n_pre)) (PreH10 : forall (edge_2: Z) , (((0 <= edge_2) /\ (edge_2 < (n_pre - 1 ))) -> ((0 <= (Znth (edge_2) (current_dist_2) (0))) /\ ((Znth (edge_2) (current_dist_2) (0)) <= 100)))) (PreH11 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station_2) (arrivals_2) (0)))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) (PreH12 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) ,
  TT && emp 
|--
  “ (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 0 0 (-1) ) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals_2) (0)))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000))) ” 
  &&  “ forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist_2) (0))) /\ ((Znth (edge) (current_dist_2) (0)) <= 100))) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (0 <= (n_pre - 1 )) ”
  &&  emp
).

Definition solve_entail_wit_13_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (k: Z) (PreH1 : (k > 0)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH6 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH7 : ((Zlength (latest_2)) = n_pre)) (PreH8 : ((Zlength (counts_2)) = n_pre)) (PreH9 : ((Zlength (arrivals_2)) = n_pre)) (PreH10 : forall (edge_2: Z) , (((0 <= edge_2) /\ (edge_2 < (n_pre - 1 ))) -> ((0 <= (Znth (edge_2) (current_dist_2) (0))) /\ ((Znth (edge_2) (current_dist_2) (0)) <= 100)))) (PreH11 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station_2) (arrivals_2) (0)))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) (PreH12 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) ,
  (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 0 0 (-1) )
.

Definition solve_entail_wit_13_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (k: Z) (PreH1 : (k > 0)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH6 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH7 : ((Zlength (latest_2)) = n_pre)) (PreH8 : ((Zlength (counts_2)) = n_pre)) (PreH9 : ((Zlength (arrivals_2)) = n_pre)) (PreH10 : forall (edge_2: Z) , (((0 <= edge_2) /\ (edge_2 < (n_pre - 1 ))) -> ((0 <= (Znth (edge_2) (current_dist_2) (0))) /\ ((Znth (edge_2) (current_dist_2) (0)) <= 100)))) (PreH11 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station_2) (arrivals_2) (0)))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) (PreH12 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) ,
  forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals_2) (0)))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))
.

Definition solve_entail_wit_13_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (k: Z) (PreH1 : (k > 0)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH6 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH7 : ((Zlength (latest_2)) = n_pre)) (PreH8 : ((Zlength (counts_2)) = n_pre)) (PreH9 : ((Zlength (arrivals_2)) = n_pre)) (PreH10 : forall (edge_2: Z) , (((0 <= edge_2) /\ (edge_2 < (n_pre - 1 ))) -> ((0 <= (Znth (edge_2) (current_dist_2) (0))) /\ ((Znth (edge_2) (current_dist_2) (0)) <= 100)))) (PreH11 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station_2) (arrivals_2) (0)))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) (PreH12 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) ,
  forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist_2) (0))) /\ ((Znth (edge) (current_dist_2) (0)) <= 100)))
.

Definition solve_entail_wit_13_split_goal_4 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (k: Z) (PreH1 : (k > 0)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH6 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH7 : ((Zlength (latest_2)) = n_pre)) (PreH8 : ((Zlength (counts_2)) = n_pre)) (PreH9 : ((Zlength (arrivals_2)) = n_pre)) (PreH10 : forall (edge_2: Z) , (((0 <= edge_2) /\ (edge_2 < (n_pre - 1 ))) -> ((0 <= (Znth (edge_2) (current_dist_2) (0))) /\ ((Znth (edge_2) (current_dist_2) (0)) <= 100)))) (PreH11 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station_2) (arrivals_2) (0)))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) (PreH12 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) ,
  (0 <= m_pre)
.

Definition solve_entail_wit_13_split_goal_5 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (k: Z) (PreH1 : (k > 0)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH6 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH7 : ((Zlength (latest_2)) = n_pre)) (PreH8 : ((Zlength (counts_2)) = n_pre)) (PreH9 : ((Zlength (arrivals_2)) = n_pre)) (PreH10 : forall (edge_2: Z) , (((0 <= edge_2) /\ (edge_2 < (n_pre - 1 ))) -> ((0 <= (Znth (edge_2) (current_dist_2) (0))) /\ ((Znth (edge_2) (current_dist_2) (0)) <= 100)))) (PreH11 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station_2) (arrivals_2) (0)))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) (PreH12 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) ,
  (0 <= (n_pre - 1 ))
.

Definition solve_entail_wit_14 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : ((Znth i current_dist_2 0) > 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH14 : ((Zlength (latest_2)) = n_pre)) (PreH15 : ((Zlength (counts_2)) = n_pre)) (PreH16 : ((Zlength (arrivals_2)) = n_pre)) (PreH17 : forall (edge_2: Z) , (((0 <= edge_2) /\ (edge_2 < (n_pre - 1 ))) -> ((0 <= (Znth (edge_2) (current_dist_2) (0))) /\ ((Znth (edge_2) (current_dist_2) (0)) <= 100)))) (PreH18 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station_2) (arrivals_2) (0)))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) (PreH19 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH20 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist_2 )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest_2 )
  **  (IntArray.full off_pre n_pre counts_2 )
  **  (IntArray.full arr_pre n_pre arrivals_2 )
|--
  EX (arrivals: (@list Z))  (counts: (@list Z))  (latest: (@list Z))  (current_dist: (@list Z)) ,
  “ (0 < k) ” 
  &&  “ (k <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ ((i + 1 ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= m_pre) ” 
  &&  “ ((-1) <= pos) ” 
  &&  “ (pos < i) ” 
  &&  “ (0 < (Znth (i) (current_dist) (0))) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ ((Zlength (current_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100))) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000))) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals ) ” 
  &&  “ (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos ) ” 
  &&  “ (MarginalBenefitScan counts latest arrivals i (i + 1 ) 0 ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : ((Znth i current_dist_2 0) > 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH14 : ((Zlength (latest_2)) = n_pre)) (PreH15 : ((Zlength (counts_2)) = n_pre)) (PreH16 : ((Zlength (arrivals_2)) = n_pre)) (PreH17 : forall (edge_2: Z) , (((0 <= edge_2) /\ (edge_2 < (n_pre - 1 ))) -> ((0 <= (Znth (edge_2) (current_dist_2) (0))) /\ ((Znth (edge_2) (current_dist_2) (0)) <= 100)))) (PreH18 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station_2) (arrivals_2) (0)))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) (PreH19 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH20 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) ,
  TT && emp 
|--
  “ (MarginalBenefitScan counts_2 latest_2 arrivals_2 i (i + 1 ) 0 ) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals_2) (0)))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000))) ” 
  &&  “ forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist_2) (0))) /\ ((Znth (edge) (current_dist_2) (0)) <= 100))) ”
  &&  emp
).

Definition solve_entail_wit_14_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : ((Znth i current_dist_2 0) > 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH14 : ((Zlength (latest_2)) = n_pre)) (PreH15 : ((Zlength (counts_2)) = n_pre)) (PreH16 : ((Zlength (arrivals_2)) = n_pre)) (PreH17 : forall (edge_2: Z) , (((0 <= edge_2) /\ (edge_2 < (n_pre - 1 ))) -> ((0 <= (Znth (edge_2) (current_dist_2) (0))) /\ ((Znth (edge_2) (current_dist_2) (0)) <= 100)))) (PreH18 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station_2) (arrivals_2) (0)))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) (PreH19 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH20 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) ,
  (MarginalBenefitScan counts_2 latest_2 arrivals_2 i (i + 1 ) 0 )
.

Definition solve_entail_wit_14_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : ((Znth i current_dist_2 0) > 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH14 : ((Zlength (latest_2)) = n_pre)) (PreH15 : ((Zlength (counts_2)) = n_pre)) (PreH16 : ((Zlength (arrivals_2)) = n_pre)) (PreH17 : forall (edge_2: Z) , (((0 <= edge_2) /\ (edge_2 < (n_pre - 1 ))) -> ((0 <= (Znth (edge_2) (current_dist_2) (0))) /\ ((Znth (edge_2) (current_dist_2) (0)) <= 100)))) (PreH18 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station_2) (arrivals_2) (0)))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) (PreH19 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH20 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) ,
  forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals_2) (0)))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))
.

Definition solve_entail_wit_14_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : ((Znth i current_dist_2 0) > 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH14 : ((Zlength (latest_2)) = n_pre)) (PreH15 : ((Zlength (counts_2)) = n_pre)) (PreH16 : ((Zlength (arrivals_2)) = n_pre)) (PreH17 : forall (edge_2: Z) , (((0 <= edge_2) /\ (edge_2 < (n_pre - 1 ))) -> ((0 <= (Znth (edge_2) (current_dist_2) (0))) /\ ((Znth (edge_2) (current_dist_2) (0)) <= 100)))) (PreH18 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station_2) (arrivals_2) (0)))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) (PreH19 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH20 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) ,
  forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist_2) (0))) /\ ((Znth (edge) (current_dist_2) (0)) <= 100)))
.

Definition solve_entail_wit_15 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : ((Znth j arrivals_2 0) > (Znth j latest_2 0))) (PreH2 : (j < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i < (n_pre - 1 ))) (PreH8 : ((i + 1 ) <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (0 <= cnt)) (PreH11 : (cnt <= m_pre)) (PreH12 : (0 <= best)) (PreH13 : (best <= m_pre)) (PreH14 : ((-1) <= pos)) (PreH15 : (pos < i)) (PreH16 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH17 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH18 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH19 : ((Zlength (latest_2)) = n_pre)) (PreH20 : ((Zlength (counts_2)) = n_pre)) (PreH21 : ((Zlength (arrivals_2)) = n_pre)) (PreH22 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist_2) (0))) /\ ((Znth (edge) (current_dist_2) (0)) <= 100)))) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals_2) (0)))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))) (PreH24 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH25 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH26 : (MarginalBenefitScan counts_2 latest_2 arrivals_2 i j cnt )) ,
  (IntArray.full late_pre n_pre latest_2 )
  **  (IntArray.full arr_pre n_pre arrivals_2 )
  **  (IntArray.full off_pre n_pre counts_2 )
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist_2 )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
|--
  EX (arrivals: (@list Z))  (counts: (@list Z))  (latest: (@list Z))  (current_dist: (@list Z)) ,
  “ (0 < k) ” 
  &&  “ (k <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ ((i + 1 ) <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (0 <= (cnt + (Znth j counts_2 0) )) ” 
  &&  “ ((cnt + (Znth j counts_2 0) ) <= m_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= m_pre) ” 
  &&  “ ((-1) <= pos) ” 
  &&  “ (pos < i) ” 
  &&  “ (0 < (Znth (i) (current_dist) (0))) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ ((Zlength (current_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100))) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000))) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals ) ” 
  &&  “ (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos ) ” 
  &&  “ (MarginalBenefitScan counts latest arrivals i (j + 1 ) (cnt + (Znth j counts_2 0) ) ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : ((Znth j arrivals_2 0) > (Znth j latest_2 0))) (PreH2 : (j < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i < (n_pre - 1 ))) (PreH8 : ((i + 1 ) <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (0 <= cnt)) (PreH11 : (cnt <= m_pre)) (PreH12 : (0 <= best)) (PreH13 : (best <= m_pre)) (PreH14 : ((-1) <= pos)) (PreH15 : (pos < i)) (PreH16 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH17 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH18 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH19 : ((Zlength (latest_2)) = n_pre)) (PreH20 : ((Zlength (counts_2)) = n_pre)) (PreH21 : ((Zlength (arrivals_2)) = n_pre)) (PreH22 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist_2) (0))) /\ ((Znth (edge) (current_dist_2) (0)) <= 100)))) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals_2) (0)))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))) (PreH24 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH25 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH26 : (MarginalBenefitScan counts_2 latest_2 arrivals_2 i j cnt )) ,
  TT && emp 
|--
  “ (MarginalBenefitScan counts_2 latest_2 arrivals_2 i (j + 1 ) (cnt + (Znth j counts_2 0) ) ) ” 
  &&  “ ((cnt + (Znth j counts_2 0) ) <= m_pre) ” 
  &&  “ (0 <= (cnt + (Znth j counts_2 0) )) ”
  &&  emp
).

Definition solve_entail_wit_15_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : ((Znth j arrivals_2 0) > (Znth j latest_2 0))) (PreH2 : (j < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i < (n_pre - 1 ))) (PreH8 : ((i + 1 ) <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (0 <= cnt)) (PreH11 : (cnt <= m_pre)) (PreH12 : (0 <= best)) (PreH13 : (best <= m_pre)) (PreH14 : ((-1) <= pos)) (PreH15 : (pos < i)) (PreH16 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH17 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH18 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH19 : ((Zlength (latest_2)) = n_pre)) (PreH20 : ((Zlength (counts_2)) = n_pre)) (PreH21 : ((Zlength (arrivals_2)) = n_pre)) (PreH22 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist_2) (0))) /\ ((Znth (edge) (current_dist_2) (0)) <= 100)))) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals_2) (0)))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))) (PreH24 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH25 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH26 : (MarginalBenefitScan counts_2 latest_2 arrivals_2 i j cnt )) ,
  (MarginalBenefitScan counts_2 latest_2 arrivals_2 i (j + 1 ) (cnt + (Znth j counts_2 0) ) )
.

Definition solve_entail_wit_15_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : ((Znth j arrivals_2 0) > (Znth j latest_2 0))) (PreH2 : (j < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i < (n_pre - 1 ))) (PreH8 : ((i + 1 ) <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (0 <= cnt)) (PreH11 : (cnt <= m_pre)) (PreH12 : (0 <= best)) (PreH13 : (best <= m_pre)) (PreH14 : ((-1) <= pos)) (PreH15 : (pos < i)) (PreH16 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH17 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH18 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH19 : ((Zlength (latest_2)) = n_pre)) (PreH20 : ((Zlength (counts_2)) = n_pre)) (PreH21 : ((Zlength (arrivals_2)) = n_pre)) (PreH22 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist_2) (0))) /\ ((Znth (edge) (current_dist_2) (0)) <= 100)))) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals_2) (0)))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))) (PreH24 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH25 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH26 : (MarginalBenefitScan counts_2 latest_2 arrivals_2 i j cnt )) ,
  ((cnt + (Znth j counts_2 0) ) <= m_pre)
.

Definition solve_entail_wit_15_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : ((Znth j arrivals_2 0) > (Znth j latest_2 0))) (PreH2 : (j < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i < (n_pre - 1 ))) (PreH8 : ((i + 1 ) <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (0 <= cnt)) (PreH11 : (cnt <= m_pre)) (PreH12 : (0 <= best)) (PreH13 : (best <= m_pre)) (PreH14 : ((-1) <= pos)) (PreH15 : (pos < i)) (PreH16 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH17 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH18 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH19 : ((Zlength (latest_2)) = n_pre)) (PreH20 : ((Zlength (counts_2)) = n_pre)) (PreH21 : ((Zlength (arrivals_2)) = n_pre)) (PreH22 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist_2) (0))) /\ ((Znth (edge) (current_dist_2) (0)) <= 100)))) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals_2) (0)))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))) (PreH24 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH25 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH26 : (MarginalBenefitScan counts_2 latest_2 arrivals_2 i j cnt )) ,
  (0 <= (cnt + (Znth j counts_2 0) ))
.

Definition solve_entail_wit_16_1 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (j >= n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt <= m_pre)) (PreH11 : (0 <= best)) (PreH12 : (best <= m_pre)) (PreH13 : ((-1) <= pos)) (PreH14 : (pos < i)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH17 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH18 : ((Zlength (latest_2)) = n_pre)) (PreH19 : ((Zlength (counts_2)) = n_pre)) (PreH20 : ((Zlength (arrivals_2)) = n_pre)) (PreH21 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist_2) (0))) /\ ((Znth (edge) (current_dist_2) (0)) <= 100)))) (PreH22 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals_2) (0)))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))) (PreH23 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH24 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH25 : (MarginalBenefitScan counts_2 latest_2 arrivals_2 i j cnt )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist_2 )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest_2 )
  **  (IntArray.full off_pre n_pre counts_2 )
  **  (IntArray.full arr_pre n_pre arrivals_2 )
|--
  EX (latest: (@list Z))  (counts: (@list Z))  (arrivals: (@list Z))  (current_dist: (@list Z)) ,
  “ (0 < k) ” 
  &&  “ (k <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= m_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= m_pre) ” 
  &&  “ ((-1) <= pos) ” 
  &&  “ (pos < i) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (0 < (Znth (i) (current_dist) (0))) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals ) ” 
  &&  “ (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos ) ” 
  &&  “ (EdgeMarginalBenefit n_pre counts latest arrivals i cnt ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (j >= n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt <= m_pre)) (PreH11 : (0 <= best)) (PreH12 : (best <= m_pre)) (PreH13 : ((-1) <= pos)) (PreH14 : (pos < i)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH17 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH18 : ((Zlength (latest_2)) = n_pre)) (PreH19 : ((Zlength (counts_2)) = n_pre)) (PreH20 : ((Zlength (arrivals_2)) = n_pre)) (PreH21 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist_2) (0))) /\ ((Znth (edge) (current_dist_2) (0)) <= 100)))) (PreH22 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals_2) (0)))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))) (PreH23 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH24 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH25 : (MarginalBenefitScan counts_2 latest_2 arrivals_2 i j cnt )) ,
  TT && emp 
|--
  “ (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt ) ”
  &&  emp
).

Definition solve_entail_wit_16_1_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (j >= n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt <= m_pre)) (PreH11 : (0 <= best)) (PreH12 : (best <= m_pre)) (PreH13 : ((-1) <= pos)) (PreH14 : (pos < i)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH17 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH18 : ((Zlength (latest_2)) = n_pre)) (PreH19 : ((Zlength (counts_2)) = n_pre)) (PreH20 : ((Zlength (arrivals_2)) = n_pre)) (PreH21 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist_2) (0))) /\ ((Znth (edge) (current_dist_2) (0)) <= 100)))) (PreH22 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals_2) (0)))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))) (PreH23 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH24 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH25 : (MarginalBenefitScan counts_2 latest_2 arrivals_2 i j cnt )) ,
  (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )
.

Definition solve_entail_wit_16_2 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : ((Znth j arrivals_2 0) <= (Znth j latest_2 0))) (PreH2 : (j < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i < (n_pre - 1 ))) (PreH8 : ((i + 1 ) <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (0 <= cnt)) (PreH11 : (cnt <= m_pre)) (PreH12 : (0 <= best)) (PreH13 : (best <= m_pre)) (PreH14 : ((-1) <= pos)) (PreH15 : (pos < i)) (PreH16 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH17 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH18 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH19 : ((Zlength (latest_2)) = n_pre)) (PreH20 : ((Zlength (counts)) = n_pre)) (PreH21 : ((Zlength (arrivals_2)) = n_pre)) (PreH22 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist_2) (0))) /\ ((Znth (edge) (current_dist_2) (0)) <= 100)))) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals_2) (0)))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))) (PreH24 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts arrivals_2 )) (PreH25 : (EdgeChoicePrefix n_pre current_dist_2 counts latest_2 arrivals_2 i best pos )) (PreH26 : (MarginalBenefitScan counts latest_2 arrivals_2 i j cnt )) ,
  (IntArray.full late_pre n_pre latest_2 )
  **  (IntArray.full arr_pre n_pre arrivals_2 )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist_2 )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
|--
  EX (latest: (@list Z))  (counts_2: (@list Z))  (arrivals: (@list Z))  (current_dist: (@list Z)) ,
  “ (0 < k) ” 
  &&  “ (k <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ (0 <= (cnt + (Znth j counts 0) )) ” 
  &&  “ ((cnt + (Znth j counts 0) ) <= m_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= m_pre) ” 
  &&  “ ((-1) <= pos) ” 
  &&  “ (pos < i) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (0 < (Znth (i) (current_dist) (0))) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts_2 arrivals ) ” 
  &&  “ (EdgeChoicePrefix n_pre current_dist counts_2 latest arrivals i best pos ) ” 
  &&  “ (EdgeMarginalBenefit n_pre counts_2 latest arrivals i (cnt + (Znth j counts 0) ) ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts_2 )
  **  (IntArray.full arr_pre n_pre arrivals )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : ((Znth j arrivals_2 0) <= (Znth j latest_2 0))) (PreH2 : (j < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i < (n_pre - 1 ))) (PreH8 : ((i + 1 ) <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (0 <= cnt)) (PreH11 : (cnt <= m_pre)) (PreH12 : (0 <= best)) (PreH13 : (best <= m_pre)) (PreH14 : ((-1) <= pos)) (PreH15 : (pos < i)) (PreH16 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH17 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH18 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH19 : ((Zlength (latest_2)) = n_pre)) (PreH20 : ((Zlength (counts)) = n_pre)) (PreH21 : ((Zlength (arrivals_2)) = n_pre)) (PreH22 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist_2) (0))) /\ ((Znth (edge) (current_dist_2) (0)) <= 100)))) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals_2) (0)))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))) (PreH24 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts arrivals_2 )) (PreH25 : (EdgeChoicePrefix n_pre current_dist_2 counts latest_2 arrivals_2 i best pos )) (PreH26 : (MarginalBenefitScan counts latest_2 arrivals_2 i j cnt )) ,
  TT && emp 
|--
  “ (EdgeMarginalBenefit n_pre counts latest_2 arrivals_2 i (cnt + (Znth j counts 0) ) ) ” 
  &&  “ ((cnt + (Znth j counts 0) ) <= m_pre) ” 
  &&  “ (0 <= (cnt + (Znth j counts 0) )) ”
  &&  emp
).

Definition solve_entail_wit_16_2_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : ((Znth j arrivals_2 0) <= (Znth j latest_2 0))) (PreH2 : (j < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i < (n_pre - 1 ))) (PreH8 : ((i + 1 ) <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (0 <= cnt)) (PreH11 : (cnt <= m_pre)) (PreH12 : (0 <= best)) (PreH13 : (best <= m_pre)) (PreH14 : ((-1) <= pos)) (PreH15 : (pos < i)) (PreH16 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH17 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH18 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH19 : ((Zlength (latest_2)) = n_pre)) (PreH20 : ((Zlength (counts)) = n_pre)) (PreH21 : ((Zlength (arrivals_2)) = n_pre)) (PreH22 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist_2) (0))) /\ ((Znth (edge) (current_dist_2) (0)) <= 100)))) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals_2) (0)))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))) (PreH24 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts arrivals_2 )) (PreH25 : (EdgeChoicePrefix n_pre current_dist_2 counts latest_2 arrivals_2 i best pos )) (PreH26 : (MarginalBenefitScan counts latest_2 arrivals_2 i j cnt )) ,
  (EdgeMarginalBenefit n_pre counts latest_2 arrivals_2 i (cnt + (Znth j counts 0) ) )
.

Definition solve_entail_wit_16_2_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : ((Znth j arrivals_2 0) <= (Znth j latest_2 0))) (PreH2 : (j < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i < (n_pre - 1 ))) (PreH8 : ((i + 1 ) <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (0 <= cnt)) (PreH11 : (cnt <= m_pre)) (PreH12 : (0 <= best)) (PreH13 : (best <= m_pre)) (PreH14 : ((-1) <= pos)) (PreH15 : (pos < i)) (PreH16 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH17 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH18 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH19 : ((Zlength (latest_2)) = n_pre)) (PreH20 : ((Zlength (counts)) = n_pre)) (PreH21 : ((Zlength (arrivals_2)) = n_pre)) (PreH22 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist_2) (0))) /\ ((Znth (edge) (current_dist_2) (0)) <= 100)))) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals_2) (0)))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))) (PreH24 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts arrivals_2 )) (PreH25 : (EdgeChoicePrefix n_pre current_dist_2 counts latest_2 arrivals_2 i best pos )) (PreH26 : (MarginalBenefitScan counts latest_2 arrivals_2 i j cnt )) ,
  ((cnt + (Znth j counts 0) ) <= m_pre)
.

Definition solve_entail_wit_16_2_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : ((Znth j arrivals_2 0) <= (Znth j latest_2 0))) (PreH2 : (j < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i < (n_pre - 1 ))) (PreH8 : ((i + 1 ) <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (0 <= cnt)) (PreH11 : (cnt <= m_pre)) (PreH12 : (0 <= best)) (PreH13 : (best <= m_pre)) (PreH14 : ((-1) <= pos)) (PreH15 : (pos < i)) (PreH16 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH17 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH18 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH19 : ((Zlength (latest_2)) = n_pre)) (PreH20 : ((Zlength (counts)) = n_pre)) (PreH21 : ((Zlength (arrivals_2)) = n_pre)) (PreH22 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist_2) (0))) /\ ((Znth (edge) (current_dist_2) (0)) <= 100)))) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals_2) (0)))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))) (PreH24 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts arrivals_2 )) (PreH25 : (EdgeChoicePrefix n_pre current_dist_2 counts latest_2 arrivals_2 i best pos )) (PreH26 : (MarginalBenefitScan counts latest_2 arrivals_2 i j cnt )) ,
  (0 <= (cnt + (Znth j counts 0) ))
.

Definition solve_entail_wit_17_1 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best < cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH17 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH18 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH19 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist_2 )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest_2 )
  **  (IntArray.full off_pre n_pre counts_2 )
  **  (IntArray.full arr_pre n_pre arrivals_2 )
|--
  EX (arrivals: (@list Z))  (counts: (@list Z))  (latest: (@list Z))  (current_dist: (@list Z)) ,
  “ (0 < k) ” 
  &&  “ (k <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre - 1 )) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= m_pre) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i < (i + 1 )) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ ((Zlength (current_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100))) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000))) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals ) ” 
  &&  “ (EdgeChoicePrefix n_pre current_dist counts latest arrivals (i + 1 ) cnt i ) ”
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best < cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH17 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH18 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH19 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  TT && emp 
|--
  “ (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 (i + 1 ) cnt i ) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals_2) (0)))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000))) ” 
  &&  “ forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist_2) (0))) /\ ((Znth (edge) (current_dist_2) (0)) <= 100))) ” 
  &&  “ ((Zlength (arrivals_2)) = n_pre) ” 
  &&  “ ((Zlength (counts_2)) = n_pre) ” 
  &&  “ ((Zlength (latest_2)) = n_pre) ” 
  &&  “ ((Zlength (current_dist_2)) = (n_pre - 1 )) ”
  &&  emp
).

Definition solve_entail_wit_17_1_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best < cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH17 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH18 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH19 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 (i + 1 ) cnt i )
.

Definition solve_entail_wit_17_1_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best < cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH17 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH18 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH19 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals_2) (0)))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))
.

Definition solve_entail_wit_17_1_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best < cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH17 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH18 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH19 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist_2) (0))) /\ ((Znth (edge) (current_dist_2) (0)) <= 100)))
.

Definition solve_entail_wit_17_1_split_goal_4 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best < cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH17 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH18 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH19 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  ((Zlength (arrivals_2)) = n_pre)
.

Definition solve_entail_wit_17_1_split_goal_5 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best < cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH17 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH18 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH19 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  ((Zlength (counts_2)) = n_pre)
.

Definition solve_entail_wit_17_1_split_goal_6 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best < cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH17 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH18 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH19 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  ((Zlength (latest_2)) = n_pre)
.

Definition solve_entail_wit_17_1_split_goal_7 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best < cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH17 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH18 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH19 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  ((Zlength (current_dist_2)) = (n_pre - 1 ))
.

Definition solve_entail_wit_17_2 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best >= cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH17 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH18 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH19 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist_2 )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest_2 )
  **  (IntArray.full off_pre n_pre counts_2 )
  **  (IntArray.full arr_pre n_pre arrivals_2 )
|--
  EX (arrivals: (@list Z))  (counts: (@list Z))  (latest: (@list Z))  (current_dist: (@list Z)) ,
  “ (0 < k) ” 
  &&  “ (k <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre - 1 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= m_pre) ” 
  &&  “ ((-1) <= pos) ” 
  &&  “ (pos < (i + 1 )) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ ((Zlength (current_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100))) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000))) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals ) ” 
  &&  “ (EdgeChoicePrefix n_pre current_dist counts latest arrivals (i + 1 ) best pos ) ”
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best >= cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH17 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH18 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH19 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  TT && emp 
|--
  “ (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 (i + 1 ) best pos ) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals_2) (0)))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000))) ” 
  &&  “ forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist_2) (0))) /\ ((Znth (edge) (current_dist_2) (0)) <= 100))) ” 
  &&  “ ((Zlength (arrivals_2)) = n_pre) ” 
  &&  “ ((Zlength (counts_2)) = n_pre) ” 
  &&  “ ((Zlength (latest_2)) = n_pre) ” 
  &&  “ ((Zlength (current_dist_2)) = (n_pre - 1 )) ”
  &&  emp
).

Definition solve_entail_wit_17_2_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best >= cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH17 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH18 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH19 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 (i + 1 ) best pos )
.

Definition solve_entail_wit_17_2_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best >= cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH17 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH18 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH19 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals_2) (0)))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))
.

Definition solve_entail_wit_17_2_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best >= cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH17 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH18 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH19 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist_2) (0))) /\ ((Znth (edge) (current_dist_2) (0)) <= 100)))
.

Definition solve_entail_wit_17_2_split_goal_4 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best >= cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH17 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH18 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH19 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  ((Zlength (arrivals_2)) = n_pre)
.

Definition solve_entail_wit_17_2_split_goal_5 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best >= cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH17 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH18 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH19 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  ((Zlength (counts_2)) = n_pre)
.

Definition solve_entail_wit_17_2_split_goal_6 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best >= cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH17 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH18 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH19 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  ((Zlength (latest_2)) = n_pre)
.

Definition solve_entail_wit_17_2_split_goal_7 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best >= cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH17 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH18 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH19 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  ((Zlength (current_dist_2)) = (n_pre - 1 ))
.

Definition solve_entail_wit_17_3 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : ((Znth i current_dist_2 0) <= 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH14 : ((Zlength (latest_2)) = n_pre)) (PreH15 : ((Zlength (counts_2)) = n_pre)) (PreH16 : ((Zlength (arrivals_2)) = n_pre)) (PreH17 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist_2) (0))) /\ ((Znth (edge) (current_dist_2) (0)) <= 100)))) (PreH18 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals_2) (0)))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))) (PreH19 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH20 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist_2 )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest_2 )
  **  (IntArray.full off_pre n_pre counts_2 )
  **  (IntArray.full arr_pre n_pre arrivals_2 )
|--
  EX (arrivals: (@list Z))  (counts: (@list Z))  (latest: (@list Z))  (current_dist: (@list Z)) ,
  “ (0 < k) ” 
  &&  “ (k <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre - 1 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= m_pre) ” 
  &&  “ ((-1) <= pos) ” 
  &&  “ (pos < (i + 1 )) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ ((Zlength (current_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100))) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000))) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals ) ” 
  &&  “ (EdgeChoicePrefix n_pre current_dist counts latest arrivals (i + 1 ) best pos ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : ((Znth i current_dist_2 0) <= 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH14 : ((Zlength (latest_2)) = n_pre)) (PreH15 : ((Zlength (counts_2)) = n_pre)) (PreH16 : ((Zlength (arrivals_2)) = n_pre)) (PreH17 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist_2) (0))) /\ ((Znth (edge) (current_dist_2) (0)) <= 100)))) (PreH18 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals_2) (0)))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))) (PreH19 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH20 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) ,
  TT && emp 
|--
  “ (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 (i + 1 ) best pos ) ”
  &&  emp
).

Definition solve_entail_wit_17_3_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : ((Znth i current_dist_2 0) <= 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH14 : ((Zlength (latest_2)) = n_pre)) (PreH15 : ((Zlength (counts_2)) = n_pre)) (PreH16 : ((Zlength (arrivals_2)) = n_pre)) (PreH17 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist_2) (0))) /\ ((Znth (edge) (current_dist_2) (0)) <= 100)))) (PreH18 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals_2) (0)))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))) (PreH19 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH20 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) ,
  (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 (i + 1 ) best pos )
.

Definition solve_entail_wit_18 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best <> 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH14 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH15 : ((Zlength (latest_2)) = n_pre)) (PreH16 : ((Zlength (counts_2)) = n_pre)) (PreH17 : ((Zlength (arrivals)) = n_pre)) (PreH18 : forall (edge_2: Z) , (((0 <= edge_2) /\ (edge_2 < (n_pre - 1 ))) -> ((0 <= (Znth (edge_2) (current_dist) (0))) /\ ((Znth (edge_2) (current_dist) (0)) <= 100)))) (PreH19 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station_2) (arrivals) (0)))) /\ ((Znth (station_2) (arrivals) (0)) <= 200000)))) (PreH20 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals )) (PreH21 : (EdgeChoicePrefix n_pre current_dist counts_2 latest_2 arrivals i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) (replace_Znth (pos) (((Znth pos current_dist 0) - 1 )) (current_dist)) )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest_2 )
  **  (IntArray.full off_pre n_pre counts_2 )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  EX (counts: (@list Z))  (latest: (@list Z))  (new_arrivals: (@list Z))  (old_arrivals: (@list Z))  (new_dist: (@list Z))  (old_dist: (@list Z)) ,
  “ (0 < k) ” 
  &&  “ (k <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < (n_pre - 1 )) ” 
  &&  “ (0 < best) ” 
  &&  “ (best <= m_pre) ” 
  &&  “ ((pos + 1 ) <= (pos + 1 )) ” 
  &&  “ ((pos + 1 ) <= n_pre) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ ((Zlength (old_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (new_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (old_arrivals)) = n_pre) ” 
  &&  “ ((Zlength (new_arrivals)) = n_pre) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (new_dist) (0))) /\ ((Znth (edge) (new_dist) (0)) <= 100))) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (new_arrivals) (0)))) /\ ((Znth (station) (new_arrivals) (0)) <= 200000))) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals ) ” 
  &&  “ (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos ) ” 
  &&  “ (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos (pos + 1 ) ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) new_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre new_arrivals )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best <> 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH14 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH15 : ((Zlength (latest_2)) = n_pre)) (PreH16 : ((Zlength (counts_2)) = n_pre)) (PreH17 : ((Zlength (arrivals)) = n_pre)) (PreH18 : forall (edge_2: Z) , (((0 <= edge_2) /\ (edge_2 < (n_pre - 1 ))) -> ((0 <= (Znth (edge_2) (current_dist) (0))) /\ ((Znth (edge_2) (current_dist) (0)) <= 100)))) (PreH19 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station_2) (arrivals) (0)))) /\ ((Znth (station_2) (arrivals) (0)) <= 200000)))) (PreH20 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals )) (PreH21 : (EdgeChoicePrefix n_pre current_dist counts_2 latest_2 arrivals i best pos )) ,
  TT && emp 
|--
  EX (old_arrivals: (@list Z))  (old_dist: (@list Z)) ,
  “ (0 <= pos) ” 
  &&  “ (pos < ((Zlength (latest_2)) - 1 )) ” 
  &&  “ (0 < best) ” 
  &&  “ ((pos + 1 ) <= (pos + 1 )) ” 
  &&  “ ((pos + 1 ) <= (Zlength (latest_2))) ” 
  &&  “ ((Zlength (old_dist)) = ((Zlength (latest_2)) - 1 )) ” 
  &&  “ ((Zlength ((replace_Znth (pos) (((Znth pos current_dist 0) - 1 )) (current_dist)))) = ((Zlength (latest_2)) - 1 )) ” 
  &&  “ ((Zlength (old_arrivals)) = (Zlength (latest_2))) ” 
  &&  “ forall (edge: Z) , (((0 <= edge) /\ (edge < ((Zlength (latest_2)) - 1 ))) -> ((0 <= (Znth (edge) ((replace_Znth (pos) (((Znth pos current_dist 0) - 1 )) (current_dist))) (0))) /\ ((Znth (edge) ((replace_Znth (pos) (((Znth pos current_dist 0) - 1 )) (current_dist))) (0)) <= 100))) ” 
  &&  “ (BoosterProgress (Zlength (latest_2)) m_pre k_pre k dist times origins destinations old_dist latest_2 counts_2 old_arrivals ) ” 
  &&  “ (BestBoostChoice (Zlength (latest_2)) old_dist counts_2 latest_2 old_arrivals best pos ) ” 
  &&  “ (ArrivalRepairProgress (Zlength (latest_2)) old_dist old_arrivals (replace_Znth (pos) (((Znth pos current_dist 0) - 1 )) (current_dist)) arrivals latest_2 pos (pos + 1 ) ) ”
  &&  emp
).

Definition solve_entail_wit_19 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (new_arrivals_2: (@list Z)) (old_arrivals_2: (@list Z)) (new_dist_2: (@list Z)) (old_dist_2: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : ((Znth i (replace_Znth (i) (((Znth i new_arrivals_2 0) - 1 )) (new_arrivals_2)) 0) >= (Znth i latest_2 0))) (PreH2 : (i < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= pos)) (PreH7 : (pos < (n_pre - 1 ))) (PreH8 : (0 < best)) (PreH9 : (best <= m_pre)) (PreH10 : ((pos + 1 ) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : ((Zlength (old_dist_2)) = (n_pre - 1 ))) (PreH14 : ((Zlength (new_dist_2)) = (n_pre - 1 ))) (PreH15 : ((Zlength (old_arrivals_2)) = n_pre)) (PreH16 : ((Zlength (new_arrivals_2)) = n_pre)) (PreH17 : ((Zlength (latest_2)) = n_pre)) (PreH18 : ((Zlength (counts_2)) = n_pre)) (PreH19 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (new_dist_2) (0))) /\ ((Znth (edge) (new_dist_2) (0)) <= 100)))) (PreH20 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station) (new_arrivals_2) (0)))) /\ ((Znth (station) (new_arrivals_2) (0)) <= 200000)))) (PreH21 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist_2 latest_2 counts_2 old_arrivals_2 )) (PreH22 : (BestBoostChoice n_pre old_dist_2 counts_2 latest_2 old_arrivals_2 best pos )) (PreH23 : (ArrivalRepairProgress n_pre old_dist_2 old_arrivals_2 new_dist_2 new_arrivals_2 latest_2 pos i )) ,
  (IntArray.full late_pre n_pre latest_2 )
  **  (IntArray.full arr_pre n_pre (replace_Znth (i) (((Znth i new_arrivals_2 0) - 1 )) (new_arrivals_2)) )
  **  (IntArray.full d_pre (n_pre - 1 ) new_dist_2 )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full off_pre n_pre counts_2 )
|--
  EX (counts: (@list Z))  (latest: (@list Z))  (new_arrivals: (@list Z))  (old_arrivals: (@list Z))  (new_dist: (@list Z))  (old_dist: (@list Z)) ,
  “ (0 < k) ” 
  &&  “ (k <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < (n_pre - 1 )) ” 
  &&  “ (0 < best) ” 
  &&  “ (best <= m_pre) ” 
  &&  “ ((pos + 1 ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ ((Zlength (old_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (new_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (old_arrivals)) = n_pre) ” 
  &&  “ ((Zlength (new_arrivals)) = n_pre) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (new_dist) (0))) /\ ((Znth (edge) (new_dist) (0)) <= 100))) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (new_arrivals) (0)))) /\ ((Znth (station) (new_arrivals) (0)) <= 200000))) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals ) ” 
  &&  “ (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos ) ” 
  &&  “ (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos (i + 1 ) ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) new_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre new_arrivals )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (new_arrivals_2: (@list Z)) (old_arrivals_2: (@list Z)) (new_dist_2: (@list Z)) (old_dist_2: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : ((Znth i (replace_Znth (i) (((Znth i new_arrivals_2 0) - 1 )) (new_arrivals_2)) 0) >= (Znth i latest_2 0))) (PreH2 : (i < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= pos)) (PreH7 : (pos < (n_pre - 1 ))) (PreH8 : (0 < best)) (PreH9 : (best <= m_pre)) (PreH10 : ((pos + 1 ) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : ((Zlength (old_dist_2)) = (n_pre - 1 ))) (PreH14 : ((Zlength (new_dist_2)) = (n_pre - 1 ))) (PreH15 : ((Zlength (old_arrivals_2)) = n_pre)) (PreH16 : ((Zlength (new_arrivals_2)) = n_pre)) (PreH17 : ((Zlength (latest_2)) = n_pre)) (PreH18 : ((Zlength (counts_2)) = n_pre)) (PreH19 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (new_dist_2) (0))) /\ ((Znth (edge) (new_dist_2) (0)) <= 100)))) (PreH20 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station) (new_arrivals_2) (0)))) /\ ((Znth (station) (new_arrivals_2) (0)) <= 200000)))) (PreH21 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist_2 latest_2 counts_2 old_arrivals_2 )) (PreH22 : (BestBoostChoice n_pre old_dist_2 counts_2 latest_2 old_arrivals_2 best pos )) (PreH23 : (ArrivalRepairProgress n_pre old_dist_2 old_arrivals_2 new_dist_2 new_arrivals_2 latest_2 pos i )) ,
  TT && emp 
|--
  EX (old_arrivals: (@list Z))  (old_dist: (@list Z)) ,
  “ ((pos + 1 ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (old_arrivals_2))) ” 
  &&  “ ((Zlength (old_dist)) = ((Zlength (old_arrivals_2)) - 1 )) ” 
  &&  “ ((Zlength (old_arrivals)) = (Zlength (old_arrivals_2))) ” 
  &&  “ ((Zlength ((replace_Znth (i) (((Znth i new_arrivals_2 0) - 1 )) (new_arrivals_2)))) = (Zlength (old_arrivals_2))) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < (Zlength (old_arrivals_2)))) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station) ((replace_Znth (i) (((Znth i new_arrivals_2 0) - 1 )) (new_arrivals_2))) (0)))) /\ ((Znth (station) ((replace_Znth (i) (((Znth i new_arrivals_2 0) - 1 )) (new_arrivals_2))) (0)) <= 200000))) ” 
  &&  “ (BoosterProgress (Zlength (old_arrivals_2)) m_pre k_pre k dist times origins destinations old_dist latest_2 counts_2 old_arrivals ) ” 
  &&  “ (BestBoostChoice (Zlength (old_arrivals_2)) old_dist counts_2 latest_2 old_arrivals best pos ) ” 
  &&  “ (ArrivalRepairProgress (Zlength (old_arrivals_2)) old_dist old_arrivals new_dist_2 (replace_Znth (i) (((Znth i new_arrivals_2 0) - 1 )) (new_arrivals_2)) latest_2 pos (i + 1 ) ) ”
  &&  emp
).

Definition solve_entail_wit_20_1 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (new_arrivals_2: (@list Z)) (old_arrivals_2: (@list Z)) (new_dist_2: (@list Z)) (old_dist_2: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= pos)) (PreH6 : (pos < (n_pre - 1 ))) (PreH7 : (0 < best)) (PreH8 : (best <= m_pre)) (PreH9 : ((pos + 1 ) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH12 : ((Zlength (old_dist_2)) = (n_pre - 1 ))) (PreH13 : ((Zlength (new_dist_2)) = (n_pre - 1 ))) (PreH14 : ((Zlength (old_arrivals_2)) = n_pre)) (PreH15 : ((Zlength (new_arrivals_2)) = n_pre)) (PreH16 : ((Zlength (latest_2)) = n_pre)) (PreH17 : ((Zlength (counts_2)) = n_pre)) (PreH18 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (new_dist_2) (0))) /\ ((Znth (edge) (new_dist_2) (0)) <= 100)))) (PreH19 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station) (new_arrivals_2) (0)))) /\ ((Znth (station) (new_arrivals_2) (0)) <= 200000)))) (PreH20 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist_2 latest_2 counts_2 old_arrivals_2 )) (PreH21 : (BestBoostChoice n_pre old_dist_2 counts_2 latest_2 old_arrivals_2 best pos )) (PreH22 : (ArrivalRepairProgress n_pre old_dist_2 old_arrivals_2 new_dist_2 new_arrivals_2 latest_2 pos i )) ,
  (IntArray.full d_pre (n_pre - 1 ) new_dist_2 )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest_2 )
  **  (IntArray.full off_pre n_pre counts_2 )
  **  (IntArray.full arr_pre n_pre new_arrivals_2 )
|--
  EX (old_dist: (@list Z))  (latest: (@list Z))  (counts: (@list Z))  (old_arrivals: (@list Z))  (new_arrivals: (@list Z))  (new_dist: (@list Z)) ,
  “ (0 < k) ” 
  &&  “ (k <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < (n_pre - 1 )) ” 
  &&  “ (0 < best) ” 
  &&  “ (best <= m_pre) ” 
  &&  “ ((pos + 1 ) <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (new_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (new_arrivals)) = n_pre) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals ) ” 
  &&  “ (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos ) ” 
  &&  “ (ArrivalRepairOutcome n_pre old_dist old_arrivals new_dist new_arrivals latest pos ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) new_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre new_arrivals )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (new_arrivals_2: (@list Z)) (old_arrivals_2: (@list Z)) (new_dist_2: (@list Z)) (old_dist_2: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= pos)) (PreH6 : (pos < (n_pre - 1 ))) (PreH7 : (0 < best)) (PreH8 : (best <= m_pre)) (PreH9 : ((pos + 1 ) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH12 : ((Zlength (old_dist_2)) = (n_pre - 1 ))) (PreH13 : ((Zlength (new_dist_2)) = (n_pre - 1 ))) (PreH14 : ((Zlength (old_arrivals_2)) = n_pre)) (PreH15 : ((Zlength (new_arrivals_2)) = n_pre)) (PreH16 : ((Zlength (latest_2)) = n_pre)) (PreH17 : ((Zlength (counts_2)) = n_pre)) (PreH18 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (new_dist_2) (0))) /\ ((Znth (edge) (new_dist_2) (0)) <= 100)))) (PreH19 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station) (new_arrivals_2) (0)))) /\ ((Znth (station) (new_arrivals_2) (0)) <= 200000)))) (PreH20 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist_2 latest_2 counts_2 old_arrivals_2 )) (PreH21 : (BestBoostChoice n_pre old_dist_2 counts_2 latest_2 old_arrivals_2 best pos )) (PreH22 : (ArrivalRepairProgress n_pre old_dist_2 old_arrivals_2 new_dist_2 new_arrivals_2 latest_2 pos i )) ,
  TT && emp 
|--
  EX (old_dist: (@list Z))  (old_arrivals: (@list Z)) ,
  “ (BoosterProgress (Zlength (old_arrivals_2)) m_pre k_pre k dist times origins destinations old_dist latest_2 counts_2 old_arrivals ) ” 
  &&  “ (BestBoostChoice (Zlength (old_arrivals_2)) old_dist counts_2 latest_2 old_arrivals best pos ) ” 
  &&  “ (ArrivalRepairOutcome (Zlength (old_arrivals_2)) old_dist old_arrivals new_dist_2 new_arrivals_2 latest_2 pos ) ”
  &&  emp
).

Definition solve_entail_wit_20_2 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (new_arrivals_2: (@list Z)) (old_arrivals_2: (@list Z)) (new_dist_2: (@list Z)) (old_dist_2: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : ((Znth i (replace_Znth (i) (((Znth i new_arrivals_2 0) - 1 )) (new_arrivals_2)) 0) < (Znth i latest_2 0))) (PreH2 : (i < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= pos)) (PreH7 : (pos < (n_pre - 1 ))) (PreH8 : (0 < best)) (PreH9 : (best <= m_pre)) (PreH10 : ((pos + 1 ) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : ((Zlength (old_dist_2)) = (n_pre - 1 ))) (PreH14 : ((Zlength (new_dist_2)) = (n_pre - 1 ))) (PreH15 : ((Zlength (old_arrivals_2)) = n_pre)) (PreH16 : ((Zlength (new_arrivals_2)) = n_pre)) (PreH17 : ((Zlength (latest_2)) = n_pre)) (PreH18 : ((Zlength (counts_2)) = n_pre)) (PreH19 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (new_dist_2) (0))) /\ ((Znth (edge) (new_dist_2) (0)) <= 100)))) (PreH20 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station) (new_arrivals_2) (0)))) /\ ((Znth (station) (new_arrivals_2) (0)) <= 200000)))) (PreH21 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist_2 latest_2 counts_2 old_arrivals_2 )) (PreH22 : (BestBoostChoice n_pre old_dist_2 counts_2 latest_2 old_arrivals_2 best pos )) (PreH23 : (ArrivalRepairProgress n_pre old_dist_2 old_arrivals_2 new_dist_2 new_arrivals_2 latest_2 pos i )) ,
  (IntArray.full late_pre n_pre latest_2 )
  **  (IntArray.full arr_pre n_pre (replace_Znth (i) (((Znth i new_arrivals_2 0) - 1 )) (new_arrivals_2)) )
  **  (IntArray.full d_pre (n_pre - 1 ) new_dist_2 )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full off_pre n_pre counts_2 )
|--
  EX (old_dist: (@list Z))  (latest: (@list Z))  (counts: (@list Z))  (old_arrivals: (@list Z))  (new_arrivals: (@list Z))  (new_dist: (@list Z)) ,
  “ (0 < k) ” 
  &&  “ (k <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < (n_pre - 1 )) ” 
  &&  “ (0 < best) ” 
  &&  “ (best <= m_pre) ” 
  &&  “ ((pos + 1 ) <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (new_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (new_arrivals)) = n_pre) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals ) ” 
  &&  “ (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos ) ” 
  &&  “ (ArrivalRepairOutcome n_pre old_dist old_arrivals new_dist new_arrivals latest pos ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) new_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre new_arrivals )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (new_arrivals_2: (@list Z)) (old_arrivals_2: (@list Z)) (new_dist_2: (@list Z)) (old_dist_2: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : ((Znth i (replace_Znth (i) (((Znth i new_arrivals_2 0) - 1 )) (new_arrivals_2)) 0) < (Znth i latest_2 0))) (PreH2 : (i < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= pos)) (PreH7 : (pos < (n_pre - 1 ))) (PreH8 : (0 < best)) (PreH9 : (best <= m_pre)) (PreH10 : ((pos + 1 ) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : ((Zlength (old_dist_2)) = (n_pre - 1 ))) (PreH14 : ((Zlength (new_dist_2)) = (n_pre - 1 ))) (PreH15 : ((Zlength (old_arrivals_2)) = n_pre)) (PreH16 : ((Zlength (new_arrivals_2)) = n_pre)) (PreH17 : ((Zlength (latest_2)) = n_pre)) (PreH18 : ((Zlength (counts_2)) = n_pre)) (PreH19 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (new_dist_2) (0))) /\ ((Znth (edge) (new_dist_2) (0)) <= 100)))) (PreH20 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station) (new_arrivals_2) (0)))) /\ ((Znth (station) (new_arrivals_2) (0)) <= 200000)))) (PreH21 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist_2 latest_2 counts_2 old_arrivals_2 )) (PreH22 : (BestBoostChoice n_pre old_dist_2 counts_2 latest_2 old_arrivals_2 best pos )) (PreH23 : (ArrivalRepairProgress n_pre old_dist_2 old_arrivals_2 new_dist_2 new_arrivals_2 latest_2 pos i )) ,
  TT && emp 
|--
  EX (old_dist: (@list Z))  (old_arrivals: (@list Z)) ,
  “ ((Zlength ((replace_Znth (i) (((Znth i new_arrivals_2 0) - 1 )) (new_arrivals_2)))) = (Zlength (old_arrivals_2))) ” 
  &&  “ (BoosterProgress (Zlength (old_arrivals_2)) m_pre k_pre k dist times origins destinations old_dist latest_2 counts_2 old_arrivals ) ” 
  &&  “ (BestBoostChoice (Zlength (old_arrivals_2)) old_dist counts_2 latest_2 old_arrivals best pos ) ” 
  &&  “ (ArrivalRepairOutcome (Zlength (old_arrivals_2)) old_dist old_arrivals new_dist_2 (replace_Znth (i) (((Znth i new_arrivals_2 0) - 1 )) (new_arrivals_2)) latest_2 pos ) ”
  &&  emp
).

Definition solve_entail_wit_21 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (old_dist_2: (@list Z)) (old_arrivals_2: (@list Z)) (new_dist_2: (@list Z)) (new_arrivals_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (k: Z) (pos: Z) (best: Z) (i: Z) (PreH1 : (0 < k)) (PreH2 : (k <= k_pre)) (PreH3 : (k_pre <= 100000)) (PreH4 : (0 <= pos)) (PreH5 : (pos < (n_pre - 1 ))) (PreH6 : (0 < best)) (PreH7 : (best <= m_pre)) (PreH8 : ((pos + 1 ) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (new_dist_2)) = (n_pre - 1 ))) (PreH11 : ((Zlength (new_arrivals_2)) = n_pre)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist_2 latest_2 counts_2 old_arrivals_2 )) (PreH14 : (BestBoostChoice n_pre old_dist_2 counts_2 latest_2 old_arrivals_2 best pos )) (PreH15 : (ArrivalRepairOutcome n_pre old_dist_2 old_arrivals_2 new_dist_2 new_arrivals_2 latest_2 pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) new_dist_2 )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest_2 )
  **  (IntArray.full off_pre n_pre counts_2 )
  **  (IntArray.full arr_pre n_pre new_arrivals_2 )
|--
  EX (old_dist: (@list Z))  (latest: (@list Z))  (counts: (@list Z))  (old_arrivals: (@list Z))  (new_arrivals: (@list Z))  (new_dist: (@list Z)) ,
  “ (0 < k) ” 
  &&  “ (k <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < (n_pre - 1 )) ” 
  &&  “ (0 < best) ” 
  &&  “ (best <= m_pre) ” 
  &&  “ ((pos + 1 ) <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (new_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (new_arrivals)) = n_pre) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals ) ” 
  &&  “ (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos ) ” 
  &&  “ (SelectedExchangeCertificate n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals best ) ” 
  &&  “ (ArrivalRepairOutcome n_pre old_dist old_arrivals new_dist new_arrivals latest pos ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) new_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre new_arrivals )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (old_dist_2: (@list Z)) (old_arrivals_2: (@list Z)) (new_dist_2: (@list Z)) (new_arrivals_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (k: Z) (pos: Z) (best: Z) (i: Z) (PreH1 : (0 < k)) (PreH2 : (k <= k_pre)) (PreH3 : (k_pre <= 100000)) (PreH4 : (0 <= pos)) (PreH5 : (pos < (n_pre - 1 ))) (PreH6 : (0 < best)) (PreH7 : (best <= m_pre)) (PreH8 : ((pos + 1 ) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (new_dist_2)) = (n_pre - 1 ))) (PreH11 : ((Zlength (new_arrivals_2)) = n_pre)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist_2 latest_2 counts_2 old_arrivals_2 )) (PreH14 : (BestBoostChoice n_pre old_dist_2 counts_2 latest_2 old_arrivals_2 best pos )) (PreH15 : (ArrivalRepairOutcome n_pre old_dist_2 old_arrivals_2 new_dist_2 new_arrivals_2 latest_2 pos )) ,
  TT && emp 
|--
  EX (old_dist: (@list Z))  (old_arrivals: (@list Z)) ,
  “ (BoosterProgress (Zlength (new_arrivals_2)) m_pre k_pre k dist times origins destinations old_dist latest_2 counts_2 old_arrivals ) ” 
  &&  “ (BestBoostChoice (Zlength (new_arrivals_2)) old_dist counts_2 latest_2 old_arrivals best pos ) ” 
  &&  “ (SelectedExchangeCertificate (Zlength (new_arrivals_2)) m_pre k_pre k dist times origins destinations old_dist latest_2 counts_2 old_arrivals best ) ” 
  &&  “ (ArrivalRepairOutcome (Zlength (new_arrivals_2)) old_dist old_arrivals new_dist_2 new_arrivals_2 latest_2 pos ) ”
  &&  emp
).

Definition solve_entail_wit_22 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (old_dist: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (new_arrivals: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (k: Z) (pos: Z) (best: Z) (i: Z) (PreH1 : (0 < k)) (PreH2 : (k <= k_pre)) (PreH3 : (k_pre <= 100000)) (PreH4 : (0 <= pos)) (PreH5 : (pos < (n_pre - 1 ))) (PreH6 : (0 < best)) (PreH7 : (best <= m_pre)) (PreH8 : ((pos + 1 ) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH11 : ((Zlength (new_arrivals)) = n_pre)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest_2 counts_2 old_arrivals )) (PreH14 : (BestBoostChoice n_pre old_dist counts_2 latest_2 old_arrivals best pos )) (PreH15 : (SelectedExchangeCertificate n_pre m_pre k_pre k dist times origins destinations old_dist latest_2 counts_2 old_arrivals best )) (PreH16 : (ArrivalRepairOutcome n_pre old_dist old_arrivals new_dist new_arrivals latest_2 pos )) ,
  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full d_pre (n_pre - 1 ) new_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest_2 )
  **  (IntArray.full off_pre n_pre counts_2 )
  **  (IntArray.full arr_pre n_pre new_arrivals )
|--
  EX (arrivals: (@list Z))  (counts: (@list Z))  (latest: (@list Z))  (current_dist: (@list Z)) ,
  “ (0 <= (k - 1 )) ” 
  &&  “ ((k - 1 ) <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ ((Zlength (current_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100))) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000))) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre (k - 1 ) dist times origins destinations current_dist latest counts arrivals ) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (old_dist: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (new_arrivals: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (k: Z) (pos: Z) (best: Z) (i: Z) (PreH1 : (0 < k)) (PreH2 : (k <= k_pre)) (PreH3 : (k_pre <= 100000)) (PreH4 : (0 <= pos)) (PreH5 : (pos < (n_pre - 1 ))) (PreH6 : (0 < best)) (PreH7 : (best <= m_pre)) (PreH8 : ((pos + 1 ) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH11 : ((Zlength (new_arrivals)) = n_pre)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest_2 counts_2 old_arrivals )) (PreH14 : (BestBoostChoice n_pre old_dist counts_2 latest_2 old_arrivals best pos )) (PreH15 : (SelectedExchangeCertificate n_pre m_pre k_pre k dist times origins destinations old_dist latest_2 counts_2 old_arrivals best )) (PreH16 : (ArrivalRepairOutcome n_pre old_dist old_arrivals new_dist new_arrivals latest_2 pos )) ,
  TT && emp 
|--
  “ (BoosterProgress n_pre m_pre k_pre (k - 1 ) dist times origins destinations new_dist latest_2 counts_2 new_arrivals ) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station) (new_arrivals) (0)))) /\ ((Znth (station) (new_arrivals) (0)) <= 200000))) ” 
  &&  “ forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (new_dist) (0))) /\ ((Znth (edge) (new_dist) (0)) <= 100))) ” 
  &&  “ ((Zlength (counts_2)) = n_pre) ” 
  &&  “ ((Zlength (latest_2)) = n_pre) ”
  &&  emp
).

Definition solve_entail_wit_22_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (old_dist: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (new_arrivals: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (k: Z) (pos: Z) (best: Z) (i: Z) (PreH1 : (0 < k)) (PreH2 : (k <= k_pre)) (PreH3 : (k_pre <= 100000)) (PreH4 : (0 <= pos)) (PreH5 : (pos < (n_pre - 1 ))) (PreH6 : (0 < best)) (PreH7 : (best <= m_pre)) (PreH8 : ((pos + 1 ) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH11 : ((Zlength (new_arrivals)) = n_pre)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest_2 counts_2 old_arrivals )) (PreH14 : (BestBoostChoice n_pre old_dist counts_2 latest_2 old_arrivals best pos )) (PreH15 : (SelectedExchangeCertificate n_pre m_pre k_pre k dist times origins destinations old_dist latest_2 counts_2 old_arrivals best )) (PreH16 : (ArrivalRepairOutcome n_pre old_dist old_arrivals new_dist new_arrivals latest_2 pos )) ,
  (BoosterProgress n_pre m_pre k_pre (k - 1 ) dist times origins destinations new_dist latest_2 counts_2 new_arrivals )
.

Definition solve_entail_wit_22_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (old_dist: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (new_arrivals: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (k: Z) (pos: Z) (best: Z) (i: Z) (PreH1 : (0 < k)) (PreH2 : (k <= k_pre)) (PreH3 : (k_pre <= 100000)) (PreH4 : (0 <= pos)) (PreH5 : (pos < (n_pre - 1 ))) (PreH6 : (0 < best)) (PreH7 : (best <= m_pre)) (PreH8 : ((pos + 1 ) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH11 : ((Zlength (new_arrivals)) = n_pre)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest_2 counts_2 old_arrivals )) (PreH14 : (BestBoostChoice n_pre old_dist counts_2 latest_2 old_arrivals best pos )) (PreH15 : (SelectedExchangeCertificate n_pre m_pre k_pre k dist times origins destinations old_dist latest_2 counts_2 old_arrivals best )) (PreH16 : (ArrivalRepairOutcome n_pre old_dist old_arrivals new_dist new_arrivals latest_2 pos )) ,
  forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station) (new_arrivals) (0)))) /\ ((Znth (station) (new_arrivals) (0)) <= 200000)))
.

Definition solve_entail_wit_22_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (old_dist: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (new_arrivals: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (k: Z) (pos: Z) (best: Z) (i: Z) (PreH1 : (0 < k)) (PreH2 : (k <= k_pre)) (PreH3 : (k_pre <= 100000)) (PreH4 : (0 <= pos)) (PreH5 : (pos < (n_pre - 1 ))) (PreH6 : (0 < best)) (PreH7 : (best <= m_pre)) (PreH8 : ((pos + 1 ) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH11 : ((Zlength (new_arrivals)) = n_pre)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest_2 counts_2 old_arrivals )) (PreH14 : (BestBoostChoice n_pre old_dist counts_2 latest_2 old_arrivals best pos )) (PreH15 : (SelectedExchangeCertificate n_pre m_pre k_pre k dist times origins destinations old_dist latest_2 counts_2 old_arrivals best )) (PreH16 : (ArrivalRepairOutcome n_pre old_dist old_arrivals new_dist new_arrivals latest_2 pos )) ,
  forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (new_dist) (0))) /\ ((Znth (edge) (new_dist) (0)) <= 100)))
.

Definition solve_entail_wit_22_split_goal_4 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (old_dist: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (new_arrivals: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (k: Z) (pos: Z) (best: Z) (i: Z) (PreH1 : (0 < k)) (PreH2 : (k <= k_pre)) (PreH3 : (k_pre <= 100000)) (PreH4 : (0 <= pos)) (PreH5 : (pos < (n_pre - 1 ))) (PreH6 : (0 < best)) (PreH7 : (best <= m_pre)) (PreH8 : ((pos + 1 ) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH11 : ((Zlength (new_arrivals)) = n_pre)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest_2 counts_2 old_arrivals )) (PreH14 : (BestBoostChoice n_pre old_dist counts_2 latest_2 old_arrivals best pos )) (PreH15 : (SelectedExchangeCertificate n_pre m_pre k_pre k dist times origins destinations old_dist latest_2 counts_2 old_arrivals best )) (PreH16 : (ArrivalRepairOutcome n_pre old_dist old_arrivals new_dist new_arrivals latest_2 pos )) ,
  ((Zlength (counts_2)) = n_pre)
.

Definition solve_entail_wit_22_split_goal_5 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (old_dist: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (new_arrivals: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (k: Z) (pos: Z) (best: Z) (i: Z) (PreH1 : (0 < k)) (PreH2 : (k <= k_pre)) (PreH3 : (k_pre <= 100000)) (PreH4 : (0 <= pos)) (PreH5 : (pos < (n_pre - 1 ))) (PreH6 : (0 < best)) (PreH7 : (best <= m_pre)) (PreH8 : ((pos + 1 ) <= i)) (PreH9 : (i <= n_pre)) (PreH10 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH11 : ((Zlength (new_arrivals)) = n_pre)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest_2 counts_2 old_arrivals )) (PreH14 : (BestBoostChoice n_pre old_dist counts_2 latest_2 old_arrivals best pos )) (PreH15 : (SelectedExchangeCertificate n_pre m_pre k_pre k dist times origins destinations old_dist latest_2 counts_2 old_arrivals best )) (PreH16 : (ArrivalRepairOutcome n_pre old_dist old_arrivals new_dist new_arrivals latest_2 pos )) ,
  ((Zlength (latest_2)) = n_pre)
.

Definition solve_entail_wit_23_1 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (k: Z) (PreH1 : (k <= 0)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH6 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH7 : ((Zlength (latest_2)) = n_pre)) (PreH8 : ((Zlength (counts_2)) = n_pre)) (PreH9 : ((Zlength (arrivals_2)) = n_pre)) (PreH10 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH11 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station_2) (arrivals_2) (0)))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) (PreH12 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest_2 )
  **  (IntArray.full off_pre n_pre counts_2 )
  **  (IntArray.full arr_pre n_pre arrivals_2 )
|--
  EX (final_dist: (@list Z))  (latest: (@list Z))  (counts: (@list Z))  (arrivals: (@list Z)) ,
  “ (0 <= k) ” 
  &&  “ (k <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (0 * 200000 )) ” 
  &&  “ (0 <= 2000000000) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals ) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals) (0))) /\ ((Znth (station) (arrivals) (0)) <= 200000))) ” 
  &&  “ forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre))) ” 
  &&  “ (TravelSumPrefix m_pre times destinations arrivals 0 0 ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (k: Z) (PreH1 : (k <= 0)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH6 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH7 : ((Zlength (latest_2)) = n_pre)) (PreH8 : ((Zlength (counts_2)) = n_pre)) (PreH9 : ((Zlength (arrivals_2)) = n_pre)) (PreH10 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH11 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station_2) (arrivals_2) (0)))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) (PreH12 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )) ,
  TT && emp 
|--
  “ (TravelSumPrefix m_pre times destinations arrivals_2 0 0 ) ” 
  &&  “ forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre))) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals_2) (0))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000))) ” 
  &&  “ (OptimizedBusState n_pre m_pre k_pre dist times origins destinations current_dist latest_2 counts_2 arrivals_2 ) ” 
  &&  “ (0 <= m_pre) ”
  &&  emp
).

Definition solve_entail_wit_23_1_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (k: Z) (PreH1 : (k <= 0)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH6 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH7 : ((Zlength (latest_2)) = n_pre)) (PreH8 : ((Zlength (counts_2)) = n_pre)) (PreH9 : ((Zlength (arrivals_2)) = n_pre)) (PreH10 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH11 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station_2) (arrivals_2) (0)))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) (PreH12 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )) ,
  (TravelSumPrefix m_pre times destinations arrivals_2 0 0 )
.

Definition solve_entail_wit_23_1_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (k: Z) (PreH1 : (k <= 0)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH6 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH7 : ((Zlength (latest_2)) = n_pre)) (PreH8 : ((Zlength (counts_2)) = n_pre)) (PreH9 : ((Zlength (arrivals_2)) = n_pre)) (PreH10 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH11 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station_2) (arrivals_2) (0)))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) (PreH12 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )) ,
  forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))
.

Definition solve_entail_wit_23_1_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (k: Z) (PreH1 : (k <= 0)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH6 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH7 : ((Zlength (latest_2)) = n_pre)) (PreH8 : ((Zlength (counts_2)) = n_pre)) (PreH9 : ((Zlength (arrivals_2)) = n_pre)) (PreH10 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH11 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station_2) (arrivals_2) (0)))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) (PreH12 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )) ,
  forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals_2) (0))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))
.

Definition solve_entail_wit_23_1_split_goal_4 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (k: Z) (PreH1 : (k <= 0)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH6 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH7 : ((Zlength (latest_2)) = n_pre)) (PreH8 : ((Zlength (counts_2)) = n_pre)) (PreH9 : ((Zlength (arrivals_2)) = n_pre)) (PreH10 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH11 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station_2) (arrivals_2) (0)))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) (PreH12 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )) ,
  (OptimizedBusState n_pre m_pre k_pre dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )
.

Definition solve_entail_wit_23_1_split_goal_5 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (k: Z) (PreH1 : (k <= 0)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH6 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH7 : ((Zlength (latest_2)) = n_pre)) (PreH8 : ((Zlength (counts_2)) = n_pre)) (PreH9 : ((Zlength (arrivals_2)) = n_pre)) (PreH10 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH11 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station_2) (arrivals_2) (0)))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) (PreH12 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )) ,
  (0 <= m_pre)
.

Definition solve_entail_wit_23_2 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (pos < 0)) (PreH2 : ((i + 1 ) >= n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (latest_2)) = n_pre)) (PreH15 : ((Zlength (counts_2)) = n_pre)) (PreH16 : ((Zlength (arrivals_2)) = n_pre)) (PreH17 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH18 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station_2) (arrivals_2) (0)))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) (PreH19 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )) (PreH20 : (EdgeChoicePrefix n_pre current_dist counts_2 latest_2 arrivals_2 i best pos )) ,
  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest_2 )
  **  (IntArray.full off_pre n_pre counts_2 )
  **  (IntArray.full arr_pre n_pre arrivals_2 )
|--
  EX (final_dist: (@list Z))  (latest: (@list Z))  (counts: (@list Z))  (arrivals: (@list Z)) ,
  “ (0 <= k) ” 
  &&  “ (k <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (0 * 200000 )) ” 
  &&  “ (0 <= 2000000000) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals ) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals) (0))) /\ ((Znth (station) (arrivals) (0)) <= 200000))) ” 
  &&  “ forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre))) ” 
  &&  “ (TravelSumPrefix m_pre times destinations arrivals 0 0 ) ”
  &&  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (pos < 0)) (PreH2 : ((i + 1 ) >= n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (latest_2)) = n_pre)) (PreH15 : ((Zlength (counts_2)) = n_pre)) (PreH16 : ((Zlength (arrivals_2)) = n_pre)) (PreH17 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH18 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station_2) (arrivals_2) (0)))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) (PreH19 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )) (PreH20 : (EdgeChoicePrefix n_pre current_dist counts_2 latest_2 arrivals_2 i best pos )) ,
  TT && emp 
|--
  “ (TravelSumPrefix m_pre times destinations arrivals_2 0 0 ) ” 
  &&  “ forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre))) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals_2) (0))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000))) ” 
  &&  “ (OptimizedBusState n_pre m_pre k_pre dist times origins destinations current_dist latest_2 counts_2 arrivals_2 ) ”
  &&  emp
).

Definition solve_entail_wit_23_2_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (pos < 0)) (PreH2 : ((i + 1 ) >= n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (latest_2)) = n_pre)) (PreH15 : ((Zlength (counts_2)) = n_pre)) (PreH16 : ((Zlength (arrivals_2)) = n_pre)) (PreH17 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH18 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station_2) (arrivals_2) (0)))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) (PreH19 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )) (PreH20 : (EdgeChoicePrefix n_pre current_dist counts_2 latest_2 arrivals_2 i best pos )) ,
  (TravelSumPrefix m_pre times destinations arrivals_2 0 0 )
.

Definition solve_entail_wit_23_2_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (pos < 0)) (PreH2 : ((i + 1 ) >= n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (latest_2)) = n_pre)) (PreH15 : ((Zlength (counts_2)) = n_pre)) (PreH16 : ((Zlength (arrivals_2)) = n_pre)) (PreH17 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH18 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station_2) (arrivals_2) (0)))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) (PreH19 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )) (PreH20 : (EdgeChoicePrefix n_pre current_dist counts_2 latest_2 arrivals_2 i best pos )) ,
  forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))
.

Definition solve_entail_wit_23_2_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (pos < 0)) (PreH2 : ((i + 1 ) >= n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (latest_2)) = n_pre)) (PreH15 : ((Zlength (counts_2)) = n_pre)) (PreH16 : ((Zlength (arrivals_2)) = n_pre)) (PreH17 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH18 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station_2) (arrivals_2) (0)))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) (PreH19 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )) (PreH20 : (EdgeChoicePrefix n_pre current_dist counts_2 latest_2 arrivals_2 i best pos )) ,
  forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals_2) (0))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))
.

Definition solve_entail_wit_23_2_split_goal_4 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (pos < 0)) (PreH2 : ((i + 1 ) >= n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH13 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (latest_2)) = n_pre)) (PreH15 : ((Zlength (counts_2)) = n_pre)) (PreH16 : ((Zlength (arrivals_2)) = n_pre)) (PreH17 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH18 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station_2) (arrivals_2) (0)))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) (PreH19 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )) (PreH20 : (EdgeChoicePrefix n_pre current_dist counts_2 latest_2 arrivals_2 i best pos )) ,
  (OptimizedBusState n_pre m_pre k_pre dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )
.

Definition solve_entail_wit_23_3 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best = 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH14 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH15 : ((Zlength (latest_2)) = n_pre)) (PreH16 : ((Zlength (counts_2)) = n_pre)) (PreH17 : ((Zlength (arrivals_2)) = n_pre)) (PreH18 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH19 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station_2) (arrivals_2) (0)))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) (PreH20 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )) (PreH21 : (EdgeChoicePrefix n_pre current_dist counts_2 latest_2 arrivals_2 i best pos )) ,
  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest_2 )
  **  (IntArray.full off_pre n_pre counts_2 )
  **  (IntArray.full arr_pre n_pre arrivals_2 )
|--
  EX (final_dist: (@list Z))  (latest: (@list Z))  (counts: (@list Z))  (arrivals: (@list Z)) ,
  “ (0 <= k) ” 
  &&  “ (k <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (0 * 200000 )) ” 
  &&  “ (0 <= 2000000000) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals ) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals) (0))) /\ ((Znth (station) (arrivals) (0)) <= 200000))) ” 
  &&  “ forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre))) ” 
  &&  “ (TravelSumPrefix m_pre times destinations arrivals 0 0 ) ”
  &&  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best = 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH14 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH15 : ((Zlength (latest_2)) = n_pre)) (PreH16 : ((Zlength (counts_2)) = n_pre)) (PreH17 : ((Zlength (arrivals_2)) = n_pre)) (PreH18 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH19 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station_2) (arrivals_2) (0)))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) (PreH20 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )) (PreH21 : (EdgeChoicePrefix n_pre current_dist counts_2 latest_2 arrivals_2 i best pos )) ,
  TT && emp 
|--
  “ (TravelSumPrefix m_pre times destinations arrivals_2 0 0 ) ” 
  &&  “ forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre))) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals_2) (0))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000))) ” 
  &&  “ (OptimizedBusState n_pre m_pre k_pre dist times origins destinations current_dist latest_2 counts_2 arrivals_2 ) ”
  &&  emp
).

Definition solve_entail_wit_23_3_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best = 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH14 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH15 : ((Zlength (latest_2)) = n_pre)) (PreH16 : ((Zlength (counts_2)) = n_pre)) (PreH17 : ((Zlength (arrivals_2)) = n_pre)) (PreH18 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH19 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station_2) (arrivals_2) (0)))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) (PreH20 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )) (PreH21 : (EdgeChoicePrefix n_pre current_dist counts_2 latest_2 arrivals_2 i best pos )) ,
  (TravelSumPrefix m_pre times destinations arrivals_2 0 0 )
.

Definition solve_entail_wit_23_3_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best = 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH14 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH15 : ((Zlength (latest_2)) = n_pre)) (PreH16 : ((Zlength (counts_2)) = n_pre)) (PreH17 : ((Zlength (arrivals_2)) = n_pre)) (PreH18 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH19 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station_2) (arrivals_2) (0)))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) (PreH20 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )) (PreH21 : (EdgeChoicePrefix n_pre current_dist counts_2 latest_2 arrivals_2 i best pos )) ,
  forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))
.

Definition solve_entail_wit_23_3_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best = 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH14 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH15 : ((Zlength (latest_2)) = n_pre)) (PreH16 : ((Zlength (counts_2)) = n_pre)) (PreH17 : ((Zlength (arrivals_2)) = n_pre)) (PreH18 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH19 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station_2) (arrivals_2) (0)))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) (PreH20 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )) (PreH21 : (EdgeChoicePrefix n_pre current_dist counts_2 latest_2 arrivals_2 i best pos )) ,
  forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals_2) (0))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))
.

Definition solve_entail_wit_23_3_split_goal_4 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best = 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH14 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH15 : ((Zlength (latest_2)) = n_pre)) (PreH16 : ((Zlength (counts_2)) = n_pre)) (PreH17 : ((Zlength (arrivals_2)) = n_pre)) (PreH18 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH19 : forall (station_2: Z) , (((0 <= station_2) /\ (station_2 < n_pre)) -> ((((((0 <= (Znth (station_2) (latest_2) (0))) /\ ((Znth (station_2) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station_2) (counts_2) (0)))) /\ ((Znth (station_2) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station_2) (arrivals_2) (0)))) /\ ((Znth (station_2) (arrivals_2) (0)) <= 200000)))) (PreH20 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )) (PreH21 : (EdgeChoicePrefix n_pre current_dist counts_2 latest_2 arrivals_2 i best pos )) ,
  (OptimizedBusState n_pre m_pre k_pre dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )
.

Definition solve_entail_wit_24 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i <= m_pre)) (PreH7 : (0 <= ans)) (PreH8 : (ans <= (i * 200000 ))) (PreH9 : (ans <= 2000000000)) (PreH10 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH11 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH12 : ((Zlength (arrivals)) = n_pre)) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals) (0))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH14 : forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))) (PreH15 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ (0 <= ((Znth (i) (destinations) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (destinations) (0)) - 1 ) < n_pre) ” 
  &&  “ (ans <= INT_MAX) ” 
  &&  “ (k <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (ans >= INT_MIN) ” 
  &&  “ (k >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= (i * 200000 )) ” 
  &&  “ (ans <= 2000000000) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals ) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals) (0))) /\ ((Znth (station) (arrivals) (0)) <= 200000))) ” 
  &&  “ forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre))) ” 
  &&  “ (TravelSumPrefix m_pre times destinations arrivals i ans ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "late" ) )) # Ptr  |-> late_pre)
  **  ((( &( "off" ) )) # Ptr  |-> off_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (ans <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (k <= INT_MAX)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH21 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH22 : ((Zlength (arrivals)) = n_pre)) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals) (0))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH24 : forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))) (PreH25 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  TT && emp 
|--
  “ (((Znth (i) (destinations) (0)) - 1 ) < n_pre) ” 
  &&  “ (0 <= ((Znth (i) (destinations) (0)) - 1 )) ”
  &&  emp
).

Definition solve_entail_wit_24_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (ans <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (k <= INT_MAX)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH21 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH22 : ((Zlength (arrivals)) = n_pre)) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals) (0))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH24 : forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))) (PreH25 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  (((Znth (i) (destinations) (0)) - 1 ) < n_pre)
.

Definition solve_entail_wit_24_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (ans <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (k <= INT_MAX)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH21 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH22 : ((Zlength (arrivals)) = n_pre)) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals) (0))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH24 : forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))) (PreH25 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  (0 <= ((Znth (i) (destinations) (0)) - 1 ))
.

Definition solve_entail_wit_25 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH21 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist_2 latest_2 counts_2 arrivals_2 )) (PreH22 : ((Zlength (arrivals_2)) = n_pre)) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals_2) (0))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))) (PreH24 : forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))) (PreH25 : (TravelSumPrefix m_pre times destinations arrivals_2 i ans )) ,
  (IntArray.full t_pre m_pre times )
  **  (IntArray.full arr_pre n_pre arrivals_2 )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full d_pre (n_pre - 1 ) final_dist_2 )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full late_pre n_pre latest_2 )
  **  (IntArray.full off_pre n_pre counts_2 )
|--
  EX (final_dist: (@list Z))  (latest: (@list Z))  (counts: (@list Z))  (arrivals: (@list Z)) ,
  “ (0 <= k) ” 
  &&  “ (k <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= m_pre) ” 
  &&  “ (0 <= ((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals_2 0) ) - (Znth i times 0) )) ” 
  &&  “ (((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals_2 0) ) - (Znth i times 0) ) <= ((i + 1 ) * 200000 )) ” 
  &&  “ (((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals_2 0) ) - (Znth i times 0) ) <= 2000000000) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals ) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals) (0))) /\ ((Znth (station) (arrivals) (0)) <= 200000))) ” 
  &&  “ forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre))) ” 
  &&  “ (TravelSumPrefix m_pre times destinations arrivals (i + 1 ) ((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals_2 0) ) - (Znth i times 0) ) ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH21 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist_2 latest_2 counts_2 arrivals_2 )) (PreH22 : ((Zlength (arrivals_2)) = n_pre)) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals_2) (0))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))) (PreH24 : forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))) (PreH25 : (TravelSumPrefix m_pre times destinations arrivals_2 i ans )) ,
  TT && emp 
|--
  “ (TravelSumPrefix m_pre times destinations arrivals_2 (i + 1 ) ((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals_2 0) ) - (Znth i times 0) ) ) ” 
  &&  “ (((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals_2 0) ) - (Znth i times 0) ) <= 2000000000) ” 
  &&  “ (((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals_2 0) ) - (Znth i times 0) ) <= ((i + 1 ) * 200000 )) ” 
  &&  “ (0 <= ((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals_2 0) ) - (Znth i times 0) )) ”
  &&  emp
).

Definition solve_entail_wit_25_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH21 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist_2 latest_2 counts_2 arrivals_2 )) (PreH22 : ((Zlength (arrivals_2)) = n_pre)) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals_2) (0))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))) (PreH24 : forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))) (PreH25 : (TravelSumPrefix m_pre times destinations arrivals_2 i ans )) ,
  (TravelSumPrefix m_pre times destinations arrivals_2 (i + 1 ) ((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals_2 0) ) - (Znth i times 0) ) )
.

Definition solve_entail_wit_25_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH21 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist_2 latest_2 counts_2 arrivals_2 )) (PreH22 : ((Zlength (arrivals_2)) = n_pre)) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals_2) (0))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))) (PreH24 : forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))) (PreH25 : (TravelSumPrefix m_pre times destinations arrivals_2 i ans )) ,
  (((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals_2 0) ) - (Znth i times 0) ) <= 2000000000)
.

Definition solve_entail_wit_25_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH21 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist_2 latest_2 counts_2 arrivals_2 )) (PreH22 : ((Zlength (arrivals_2)) = n_pre)) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals_2) (0))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))) (PreH24 : forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))) (PreH25 : (TravelSumPrefix m_pre times destinations arrivals_2 i ans )) ,
  (((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals_2 0) ) - (Znth i times 0) ) <= ((i + 1 ) * 200000 ))
.

Definition solve_entail_wit_25_split_goal_4 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH21 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist_2 latest_2 counts_2 arrivals_2 )) (PreH22 : ((Zlength (arrivals_2)) = n_pre)) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals_2) (0))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))) (PreH24 : forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))) (PreH25 : (TravelSumPrefix m_pre times destinations arrivals_2 i ans )) ,
  (0 <= ((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals_2 0) ) - (Znth i times 0) ))
.

Definition solve_return_wit_1 := 
(
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (i >= m_pre)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i <= m_pre)) (PreH7 : (0 <= ans)) (PreH8 : (ans <= (i * 200000 ))) (PreH9 : (ans <= 2000000000)) (PreH10 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH11 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist_2 latest_2 counts_2 arrivals_2 )) (PreH12 : ((Zlength (arrivals_2)) = n_pre)) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals_2) (0))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))) (PreH14 : forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))) (PreH15 : (TravelSumPrefix m_pre times destinations arrivals_2 i ans )) ,
  (IntArray.full d_pre (n_pre - 1 ) final_dist_2 )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest_2 )
  **  (IntArray.full off_pre n_pre counts_2 )
  **  (IntArray.full arr_pre n_pre arrivals_2 )
|--
  EX (counts: (@list Z))  (final_dist: (@list Z))  (latest: (@list Z))  (arrivals: (@list Z)) ,
  “ (SightseeingOptimalState n_pre m_pre k_pre dist times origins destinations final_dist latest arrivals ans ) ” 
  &&  “ (DestinationCounts n_pre m_pre destinations counts ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (i >= m_pre)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i <= m_pre)) (PreH7 : (0 <= ans)) (PreH8 : (ans <= (i * 200000 ))) (PreH9 : (ans <= 2000000000)) (PreH10 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH11 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist_2 latest_2 counts_2 arrivals_2 )) (PreH12 : ((Zlength (arrivals_2)) = n_pre)) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals_2) (0))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))) (PreH14 : forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))) (PreH15 : (TravelSumPrefix m_pre times destinations arrivals_2 i ans )) ,
  TT && emp 
|--
  “ (DestinationCounts n_pre m_pre destinations counts_2 ) ” 
  &&  “ (SightseeingOptimalState n_pre m_pre k_pre dist times origins destinations final_dist_2 latest_2 arrivals_2 ans ) ”
  &&  emp
).

Definition solve_return_wit_1_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (i >= m_pre)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i <= m_pre)) (PreH7 : (0 <= ans)) (PreH8 : (ans <= (i * 200000 ))) (PreH9 : (ans <= 2000000000)) (PreH10 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH11 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist_2 latest_2 counts_2 arrivals_2 )) (PreH12 : ((Zlength (arrivals_2)) = n_pre)) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals_2) (0))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))) (PreH14 : forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))) (PreH15 : (TravelSumPrefix m_pre times destinations arrivals_2 i ans )) ,
  (DestinationCounts n_pre m_pre destinations counts_2 )
.

Definition solve_return_wit_1_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (i >= m_pre)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i <= m_pre)) (PreH7 : (0 <= ans)) (PreH8 : (ans <= (i * 200000 ))) (PreH9 : (ans <= 2000000000)) (PreH10 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH11 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist_2 latest_2 counts_2 arrivals_2 )) (PreH12 : ((Zlength (arrivals_2)) = n_pre)) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals_2) (0))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))) (PreH14 : forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))) (PreH15 : (TravelSumPrefix m_pre times destinations arrivals_2 i ans )) ,
  (SightseeingOptimalState n_pre m_pre k_pre dist times origins destinations final_dist_2 latest_2 arrivals_2 ans )
.

Definition solve_partial_solve_wit_1 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_prefix: (@list Z)) (latest_prefix: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (latest_prefix)) = i)) (PreH5 : ((Zlength (counts_prefix)) = i)) (PreH6 : (WorkspacesZeroPrefix latest_prefix counts_prefix i )) (PreH7 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH8 : (0 <= k_pre)) (PreH9 : (k_pre <= 100000)) ,
  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.seg late_pre 0 i latest_prefix )
  **  (IntArray.undef_seg late_pre i n_pre )
  **  (IntArray.seg off_pre 0 i counts_prefix )
  **  (IntArray.undef_seg off_pre i n_pre )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (latest_prefix)) = i) ” 
  &&  “ ((Zlength (counts_prefix)) = i) ” 
  &&  “ (WorkspacesZeroPrefix latest_prefix counts_prefix i ) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ”
  &&  (((late_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg late_pre (i + 1 ) n_pre )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.seg late_pre 0 i latest_prefix )
  **  (IntArray.seg off_pre 0 i counts_prefix )
  **  (IntArray.undef_seg off_pre i n_pre )
  **  (IntArray.undef_full arr_pre n_pre )
.

Definition solve_partial_solve_wit_2 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_prefix: (@list Z)) (latest_prefix: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (latest_prefix)) = i)) (PreH5 : ((Zlength (counts_prefix)) = i)) (PreH6 : (WorkspacesZeroPrefix latest_prefix counts_prefix i )) (PreH7 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH8 : (0 <= k_pre)) (PreH9 : (k_pre <= 100000)) ,
  (IntArray.seg late_pre 0 (i + 1 ) (app (latest_prefix) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg late_pre (i + 1 ) n_pre )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.seg off_pre 0 i counts_prefix )
  **  (IntArray.undef_seg off_pre i n_pre )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (latest_prefix)) = i) ” 
  &&  “ ((Zlength (counts_prefix)) = i) ” 
  &&  “ (WorkspacesZeroPrefix latest_prefix counts_prefix i ) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ”
  &&  (((off_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg off_pre (i + 1 ) n_pre )
  **  (IntArray.seg late_pre 0 (i + 1 ) (app (latest_prefix) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg late_pre (i + 1 ) n_pre )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.seg off_pre 0 i counts_prefix )
  **  (IntArray.undef_full arr_pre n_pre )
.

Definition solve_partial_solve_wit_3 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : ((Zlength (latest)) = n_pre)) (PreH8 : ((Zlength (counts)) = n_pre)) (PreH9 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH10 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ (i < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i))) ” 
  &&  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i origins 0))
  **  (IntArray.missing_i a_pre i 0 m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
.

Definition solve_partial_solve_wit_4 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : ((Zlength (latest)) = n_pre)) (PreH8 : ((Zlength (counts)) = n_pre)) (PreH9 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH10 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ (i < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i))) ” 
  &&  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts ) ”
  &&  (((b_pre + (i * sizeof(INT)))) # Int  |-> (Znth i destinations 0))
  **  (IntArray.missing_i b_pre i 0 m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
.

Definition solve_partial_solve_wit_5 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (((Znth (i) (destinations) (0)) - 1 ) = ((Znth (i) (destinations) (0)) - 1 ))) (PreH4 : (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX)) (PreH5 : (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN)) (PreH6 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH7 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH16 : (i < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= 100000)) (PreH22 : ((Zlength (latest)) = n_pre)) (PreH23 : ((Zlength (counts)) = n_pre)) (PreH24 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH25 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ (0 <= ((Znth (i) (destinations) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (destinations) (0)) - 1 ) < n_pre) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN) ” 
  &&  “ (0 <= ((Znth (i) (origins) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) < n_pre) ” 
  &&  “ (k_pre <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (((Znth i destinations 0) - 1 ) <= INT_MAX) ” 
  &&  “ (k_pre >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (((Znth i destinations 0) - 1 ) >= INT_MIN) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i))) ” 
  &&  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts ) ”
  &&  (((late_pre + (((Znth (i) (origins) (0)) - 1 ) * sizeof(INT)))) # Int  |-> (Znth ((Znth (i) (origins) (0)) - 1 ) latest 0))
  **  (IntArray.missing_i late_pre ((Znth (i) (origins) (0)) - 1 ) 0 n_pre latest )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
.

Definition solve_partial_solve_wit_6 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX)) (PreH4 : (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN)) (PreH5 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH6 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH7 : (k_pre <= INT_MAX)) (PreH8 : (m_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH11 : (k_pre >= INT_MIN)) (PreH12 : (m_pre >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH15 : (i < m_pre)) (PreH16 : (0 <= i)) (PreH17 : (i <= m_pre)) (PreH18 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH19 : (0 <= k_pre)) (PreH20 : (k_pre <= 100000)) (PreH21 : ((Zlength (latest)) = n_pre)) (PreH22 : ((Zlength (counts)) = n_pre)) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH24 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ (0 <= ((Znth (i) (destinations) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (destinations) (0)) - 1 ) < n_pre) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN) ” 
  &&  “ (0 <= ((Znth (i) (origins) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) < n_pre) ” 
  &&  “ (k_pre <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (((Znth i destinations 0) - 1 ) <= INT_MAX) ” 
  &&  “ (k_pre >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (((Znth i destinations 0) - 1 ) >= INT_MIN) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i))) ” 
  &&  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts ) ”
  &&  (((t_pre + (i * sizeof(INT)))) # Int  |-> (Znth i times 0))
  **  (IntArray.missing_i t_pre i 0 m_pre times )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
.

Definition solve_partial_solve_wit_7 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) < (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH3 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH4 : (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX)) (PreH5 : (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN)) (PreH6 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH7 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH16 : (i < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= 100000)) (PreH22 : ((Zlength (latest)) = n_pre)) (PreH23 : ((Zlength (counts)) = n_pre)) (PreH24 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH25 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full t_pre m_pre times )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) < (Znth i times 0)) ” 
  &&  “ (0 <= ((Znth (i) (destinations) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (destinations) (0)) - 1 ) < n_pre) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN) ” 
  &&  “ (0 <= ((Znth (i) (origins) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) < n_pre) ” 
  &&  “ (k_pre <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (((Znth i destinations 0) - 1 ) <= INT_MAX) ” 
  &&  “ (k_pre >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (((Znth i destinations 0) - 1 ) >= INT_MIN) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i))) ” 
  &&  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts ) ”
  &&  (((t_pre + (i * sizeof(INT)))) # Int  |-> (Znth i times 0))
  **  (IntArray.missing_i t_pre i 0 m_pre times )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
.

Definition solve_partial_solve_wit_8 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) < (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH3 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH4 : (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX)) (PreH5 : (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN)) (PreH6 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH7 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH16 : (i < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= 100000)) (PreH22 : ((Zlength (latest)) = n_pre)) (PreH23 : ((Zlength (counts)) = n_pre)) (PreH24 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH25 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full t_pre m_pre times )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) < (Znth i times 0)) ” 
  &&  “ (0 <= ((Znth (i) (destinations) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (destinations) (0)) - 1 ) < n_pre) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN) ” 
  &&  “ (0 <= ((Znth (i) (origins) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) < n_pre) ” 
  &&  “ (k_pre <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (((Znth i destinations 0) - 1 ) <= INT_MAX) ” 
  &&  “ (k_pre >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (((Znth i destinations 0) - 1 ) >= INT_MIN) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i))) ” 
  &&  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts ) ”
  &&  (((late_pre + (((Znth (i) (origins) (0)) - 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i late_pre ((Znth (i) (origins) (0)) - 1 ) 0 n_pre latest )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
.

Definition solve_partial_solve_wit_9 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) < (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH3 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH4 : (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX)) (PreH5 : (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN)) (PreH6 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH7 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH16 : (i < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= 100000)) (PreH22 : ((Zlength (latest)) = n_pre)) (PreH23 : ((Zlength (counts)) = n_pre)) (PreH24 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH25 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full late_pre n_pre (replace_Znth (((Znth (i) (origins) (0)) - 1 )) ((Znth i times 0)) (latest)) )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) < (Znth i times 0)) ” 
  &&  “ (0 <= ((Znth (i) (destinations) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (destinations) (0)) - 1 ) < n_pre) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN) ” 
  &&  “ (0 <= ((Znth (i) (origins) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) < n_pre) ” 
  &&  “ (k_pre <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (((Znth i destinations 0) - 1 ) <= INT_MAX) ” 
  &&  “ (k_pre >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (((Znth i destinations 0) - 1 ) >= INT_MIN) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i))) ” 
  &&  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts ) ”
  &&  (((off_pre + (((Znth (i) (destinations) (0)) - 1 ) * sizeof(INT)))) # Int  |-> (Znth ((Znth (i) (destinations) (0)) - 1 ) counts 0))
  **  (IntArray.missing_i off_pre ((Znth (i) (destinations) (0)) - 1 ) 0 n_pre counts )
  **  (IntArray.full late_pre n_pre (replace_Znth (((Znth (i) (origins) (0)) - 1 )) ((Znth i times 0)) (latest)) )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_full arr_pre n_pre )
.

Definition solve_partial_solve_wit_10 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) < (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH3 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH4 : (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX)) (PreH5 : (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN)) (PreH6 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH7 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH16 : (i < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= 100000)) (PreH22 : ((Zlength (latest)) = n_pre)) (PreH23 : ((Zlength (counts)) = n_pre)) (PreH24 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH25 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full late_pre n_pre (replace_Znth (((Znth (i) (origins) (0)) - 1 )) ((Znth i times 0)) (latest)) )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) < (Znth i times 0)) ” 
  &&  “ (0 <= ((Znth (i) (destinations) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (destinations) (0)) - 1 ) < n_pre) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN) ” 
  &&  “ (0 <= ((Znth (i) (origins) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) < n_pre) ” 
  &&  “ (k_pre <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (((Znth i destinations 0) - 1 ) <= INT_MAX) ” 
  &&  “ (k_pre >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (((Znth i destinations 0) - 1 ) >= INT_MIN) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i))) ” 
  &&  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts ) ”
  &&  (((off_pre + (((Znth (i) (destinations) (0)) - 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i off_pre ((Znth (i) (destinations) (0)) - 1 ) 0 n_pre counts )
  **  (IntArray.full late_pre n_pre (replace_Znth (((Znth (i) (origins) (0)) - 1 )) ((Znth i times 0)) (latest)) )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_full arr_pre n_pre )
.

Definition solve_partial_solve_wit_11 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) >= (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH3 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH4 : (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX)) (PreH5 : (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN)) (PreH6 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH7 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH16 : (i < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= 100000)) (PreH22 : ((Zlength (latest)) = n_pre)) (PreH23 : ((Zlength (counts)) = n_pre)) (PreH24 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH25 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full t_pre m_pre times )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) >= (Znth i times 0)) ” 
  &&  “ (0 <= ((Znth (i) (destinations) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (destinations) (0)) - 1 ) < n_pre) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN) ” 
  &&  “ (0 <= ((Znth (i) (origins) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) < n_pre) ” 
  &&  “ (k_pre <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (((Znth i destinations 0) - 1 ) <= INT_MAX) ” 
  &&  “ (k_pre >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (((Znth i destinations 0) - 1 ) >= INT_MIN) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i))) ” 
  &&  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts ) ”
  &&  (((off_pre + (((Znth (i) (destinations) (0)) - 1 ) * sizeof(INT)))) # Int  |-> (Znth ((Znth (i) (destinations) (0)) - 1 ) counts 0))
  **  (IntArray.missing_i off_pre ((Znth (i) (destinations) (0)) - 1 ) 0 n_pre counts )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_full arr_pre n_pre )
.

Definition solve_partial_solve_wit_12 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) >= (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH3 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH4 : (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX)) (PreH5 : (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN)) (PreH6 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH7 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH8 : (k_pre <= INT_MAX)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH12 : (k_pre >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH16 : (i < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= 100000)) (PreH22 : ((Zlength (latest)) = n_pre)) (PreH23 : ((Zlength (counts)) = n_pre)) (PreH24 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) (PreH25 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_full arr_pre n_pre )
|--
  “ ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) >= (Znth i times 0)) ” 
  &&  “ (0 <= ((Znth (i) (destinations) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (destinations) (0)) - 1 ) < n_pre) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) <= INT_MAX) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) >= INT_MIN) ” 
  &&  “ (0 <= ((Znth (i) (origins) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) < n_pre) ” 
  &&  “ (k_pre <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (((Znth i destinations 0) - 1 ) <= INT_MAX) ” 
  &&  “ (k_pre >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (((Znth i destinations 0) - 1 ) >= INT_MIN) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i))) ” 
  &&  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts ) ”
  &&  (((off_pre + (((Znth (i) (destinations) (0)) - 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i off_pre ((Znth (i) (destinations) (0)) - 1 ) 0 n_pre counts )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_full arr_pre n_pre )
.

Definition solve_partial_solve_wit_13 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= cur)) (PreH5 : (cur <= 200000)) (PreH6 : ((Zlength (arrivals_prefix)) = i)) (PreH7 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH8 : (0 <= k_pre)) (PreH9 : (k_pre <= 100000)) (PreH10 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH11 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)))) (PreH12 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.seg arr_pre 0 i arrivals_prefix )
  **  (IntArray.undef_seg arr_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= 200000) ” 
  &&  “ ((Zlength (arrivals_prefix)) = i) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (StationSummaryState n_pre m_pre times origins destinations latest counts ) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre))) ” 
  &&  “ (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur ) ”
  &&  (((arr_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg arr_pre (i + 1 ) n_pre )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.seg arr_pre 0 i arrivals_prefix )
.

Definition solve_partial_solve_wit_14 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= cur)) (PreH5 : (cur <= 200000)) (PreH6 : ((Zlength (arrivals_prefix)) = i)) (PreH7 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH8 : (0 <= k_pre)) (PreH9 : (k_pre <= 100000)) (PreH10 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH11 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)))) (PreH12 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.seg arr_pre 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg arr_pre (i + 1 ) n_pre )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= 200000) ” 
  &&  “ ((Zlength (arrivals_prefix)) = i) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (StationSummaryState n_pre m_pre times origins destinations latest counts ) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre))) ” 
  &&  “ (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur ) ”
  &&  (((late_pre + (i * sizeof(INT)))) # Int  |-> (Znth i latest 0))
  **  (IntArray.missing_i late_pre i 0 n_pre latest )
  **  (IntArray.seg arr_pre 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg arr_pre (i + 1 ) n_pre )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full off_pre n_pre counts )
.

Definition solve_partial_solve_wit_15 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : (cur < (Znth i latest 0))) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= cur)) (PreH6 : (cur <= 200000)) (PreH7 : ((Zlength (arrivals_prefix)) = i)) (PreH8 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= 100000)) (PreH11 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH12 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)))) (PreH13 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full late_pre n_pre latest )
  **  (IntArray.seg arr_pre 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg arr_pre (i + 1 ) n_pre )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ (cur < (Znth i latest 0)) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= 200000) ” 
  &&  “ ((Zlength (arrivals_prefix)) = i) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (StationSummaryState n_pre m_pre times origins destinations latest counts ) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre))) ” 
  &&  “ (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur ) ”
  &&  (((late_pre + (i * sizeof(INT)))) # Int  |-> (Znth i latest 0))
  **  (IntArray.missing_i late_pre i 0 n_pre latest )
  **  (IntArray.seg arr_pre 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg arr_pre (i + 1 ) n_pre )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full off_pre n_pre counts )
.

Definition solve_partial_solve_wit_16 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur < (Znth i latest 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix)) = i)) (PreH9 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= 100000)) (PreH12 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)))) (PreH14 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full late_pre n_pre latest )
  **  (IntArray.seg arr_pre 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg arr_pre (i + 1 ) n_pre )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ ((i + 1 ) < n_pre) ” 
  &&  “ (cur < (Znth i latest 0)) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= 200000) ” 
  &&  “ ((Zlength (arrivals_prefix)) = i) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (StationSummaryState n_pre m_pre times origins destinations latest counts ) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre))) ” 
  &&  “ (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur ) ”
  &&  (((d_pre + (i * sizeof(INT)))) # Int  |-> (Znth i dist 0))
  **  (IntArray.missing_i d_pre i 0 (n_pre - 1 ) dist )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.seg arr_pre 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg arr_pre (i + 1 ) n_pre )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full off_pre n_pre counts )
.

Definition solve_partial_solve_wit_17 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur >= (Znth i latest 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix)) = i)) (PreH9 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= 100000)) (PreH12 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)))) (PreH14 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full late_pre n_pre latest )
  **  (IntArray.seg arr_pre 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg arr_pre (i + 1 ) n_pre )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ ((i + 1 ) < n_pre) ” 
  &&  “ (cur >= (Znth i latest 0)) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= 200000) ” 
  &&  “ ((Zlength (arrivals_prefix)) = i) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (StationSummaryState n_pre m_pre times origins destinations latest counts ) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre))) ” 
  &&  “ (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur ) ”
  &&  (((d_pre + (i * sizeof(INT)))) # Int  |-> (Znth i dist 0))
  **  (IntArray.missing_i d_pre i 0 (n_pre - 1 ) dist )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.seg arr_pre 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg arr_pre (i + 1 ) n_pre )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full off_pre n_pre counts )
.

Definition solve_partial_solve_wit_18 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n_pre - 1 ))) (PreH7 : (0 <= best)) (PreH8 : (best <= m_pre)) (PreH9 : ((-1) <= pos)) (PreH10 : (pos < i)) (PreH11 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH12 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH13 : ((Zlength (latest)) = n_pre)) (PreH14 : ((Zlength (counts)) = n_pre)) (PreH15 : ((Zlength (arrivals)) = n_pre)) (PreH16 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH17 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH18 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH19 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ ((i + 1 ) < n_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 1 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= m_pre) ” 
  &&  “ ((-1) <= pos) ” 
  &&  “ (pos < i) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ ((Zlength (current_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100))) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000))) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals ) ” 
  &&  “ (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos ) ”
  &&  (((d_pre + (i * sizeof(INT)))) # Int  |-> (Znth i current_dist 0))
  **  (IntArray.missing_i d_pre i 0 (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
.

Definition solve_partial_solve_wit_19 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (j < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt <= m_pre)) (PreH11 : (0 <= best)) (PreH12 : (best <= m_pre)) (PreH13 : ((-1) <= pos)) (PreH14 : (pos < i)) (PreH15 : (0 < (Znth (i) (current_dist) (0)))) (PreH16 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH17 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH18 : ((Zlength (latest)) = n_pre)) (PreH19 : ((Zlength (counts)) = n_pre)) (PreH20 : ((Zlength (arrivals)) = n_pre)) (PreH21 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH22 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH23 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH24 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) (PreH25 : (MarginalBenefitScan counts latest arrivals i j cnt )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ (j < n_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= m_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= m_pre) ” 
  &&  “ ((-1) <= pos) ” 
  &&  “ (pos < i) ” 
  &&  “ (0 < (Znth (i) (current_dist) (0))) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ ((Zlength (current_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100))) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000))) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals ) ” 
  &&  “ (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos ) ” 
  &&  “ (MarginalBenefitScan counts latest arrivals i j cnt ) ”
  &&  (((off_pre + (j * sizeof(INT)))) # Int  |-> (Znth j counts 0))
  **  (IntArray.missing_i off_pre j 0 n_pre counts )
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full arr_pre n_pre arrivals )
.

Definition solve_partial_solve_wit_20 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (j < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt <= m_pre)) (PreH11 : (0 <= best)) (PreH12 : (best <= m_pre)) (PreH13 : ((-1) <= pos)) (PreH14 : (pos < i)) (PreH15 : (0 < (Znth (i) (current_dist) (0)))) (PreH16 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH17 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH18 : ((Zlength (latest)) = n_pre)) (PreH19 : ((Zlength (counts)) = n_pre)) (PreH20 : ((Zlength (arrivals)) = n_pre)) (PreH21 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH22 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH23 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH24 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) (PreH25 : (MarginalBenefitScan counts latest arrivals i j cnt )) ,
  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ (j < n_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= m_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= m_pre) ” 
  &&  “ ((-1) <= pos) ” 
  &&  “ (pos < i) ” 
  &&  “ (0 < (Znth (i) (current_dist) (0))) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ ((Zlength (current_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100))) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000))) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals ) ” 
  &&  “ (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos ) ” 
  &&  “ (MarginalBenefitScan counts latest arrivals i j cnt ) ”
  &&  (((arr_pre + (j * sizeof(INT)))) # Int  |-> (Znth j arrivals 0))
  **  (IntArray.missing_i arr_pre j 0 n_pre arrivals )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
.

Definition solve_partial_solve_wit_21 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (j < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt <= m_pre)) (PreH11 : (0 <= best)) (PreH12 : (best <= m_pre)) (PreH13 : ((-1) <= pos)) (PreH14 : (pos < i)) (PreH15 : (0 < (Znth (i) (current_dist) (0)))) (PreH16 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH17 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH18 : ((Zlength (latest)) = n_pre)) (PreH19 : ((Zlength (counts)) = n_pre)) (PreH20 : ((Zlength (arrivals)) = n_pre)) (PreH21 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH22 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH23 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH24 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) (PreH25 : (MarginalBenefitScan counts latest arrivals i j cnt )) ,
  (IntArray.full arr_pre n_pre arrivals )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
|--
  “ (j < n_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (n_pre - 1 )) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= m_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= m_pre) ” 
  &&  “ ((-1) <= pos) ” 
  &&  “ (pos < i) ” 
  &&  “ (0 < (Znth (i) (current_dist) (0))) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ ((Zlength (current_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100))) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000))) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals ) ” 
  &&  “ (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos ) ” 
  &&  “ (MarginalBenefitScan counts latest arrivals i j cnt ) ”
  &&  (((late_pre + (j * sizeof(INT)))) # Int  |-> (Znth j latest 0))
  **  (IntArray.missing_i late_pre j 0 n_pre latest )
  **  (IntArray.full arr_pre n_pre arrivals )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
.

Definition solve_partial_solve_wit_22 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best <> 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH14 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH15 : ((Zlength (latest)) = n_pre)) (PreH16 : ((Zlength (counts)) = n_pre)) (PreH17 : ((Zlength (arrivals)) = n_pre)) (PreH18 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH19 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH20 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH21 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ (best <> 0) ” 
  &&  “ (pos >= 0) ” 
  &&  “ ((i + 1 ) >= n_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 1 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= m_pre) ” 
  &&  “ ((-1) <= pos) ” 
  &&  “ (pos < i) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ ((Zlength (current_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100))) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000))) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals ) ” 
  &&  “ (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos ) ”
  &&  (((d_pre + (pos * sizeof(INT)))) # Int  |-> (Znth pos current_dist 0))
  **  (IntArray.missing_i d_pre pos 0 (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
.

Definition solve_partial_solve_wit_23 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best <> 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH14 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH15 : ((Zlength (latest)) = n_pre)) (PreH16 : ((Zlength (counts)) = n_pre)) (PreH17 : ((Zlength (arrivals)) = n_pre)) (PreH18 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) (PreH19 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH20 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH21 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ (best <> 0) ” 
  &&  “ (pos >= 0) ” 
  &&  “ ((i + 1 ) >= n_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 1 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= m_pre) ” 
  &&  “ ((-1) <= pos) ” 
  &&  “ (pos < i) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ ((Zlength (current_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100))) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000))) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals ) ” 
  &&  “ (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos ) ”
  &&  (((d_pre + (pos * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i d_pre pos 0 (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
.

Definition solve_partial_solve_wit_24 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (new_arrivals: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (old_dist: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= pos)) (PreH6 : (pos < (n_pre - 1 ))) (PreH7 : (0 < best)) (PreH8 : (best <= m_pre)) (PreH9 : ((pos + 1 ) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH12 : ((Zlength (old_dist)) = (n_pre - 1 ))) (PreH13 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (old_arrivals)) = n_pre)) (PreH15 : ((Zlength (new_arrivals)) = n_pre)) (PreH16 : ((Zlength (latest)) = n_pre)) (PreH17 : ((Zlength (counts)) = n_pre)) (PreH18 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (new_dist) (0))) /\ ((Znth (edge) (new_dist) (0)) <= 100)))) (PreH19 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (new_arrivals) (0)))) /\ ((Znth (station) (new_arrivals) (0)) <= 200000)))) (PreH20 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals )) (PreH21 : (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos )) (PreH22 : (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos i )) ,
  (IntArray.full d_pre (n_pre - 1 ) new_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre new_arrivals )
|--
  “ (i < n_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < (n_pre - 1 )) ” 
  &&  “ (0 < best) ” 
  &&  “ (best <= m_pre) ” 
  &&  “ ((pos + 1 ) <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ ((Zlength (old_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (new_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (old_arrivals)) = n_pre) ” 
  &&  “ ((Zlength (new_arrivals)) = n_pre) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (new_dist) (0))) /\ ((Znth (edge) (new_dist) (0)) <= 100))) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (new_arrivals) (0)))) /\ ((Znth (station) (new_arrivals) (0)) <= 200000))) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals ) ” 
  &&  “ (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos ) ” 
  &&  “ (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos i ) ”
  &&  (((arr_pre + (i * sizeof(INT)))) # Int  |-> (Znth i new_arrivals 0))
  **  (IntArray.missing_i arr_pre i 0 n_pre new_arrivals )
  **  (IntArray.full d_pre (n_pre - 1 ) new_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
.

Definition solve_partial_solve_wit_25 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (new_arrivals: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (old_dist: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= pos)) (PreH6 : (pos < (n_pre - 1 ))) (PreH7 : (0 < best)) (PreH8 : (best <= m_pre)) (PreH9 : ((pos + 1 ) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH12 : ((Zlength (old_dist)) = (n_pre - 1 ))) (PreH13 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (old_arrivals)) = n_pre)) (PreH15 : ((Zlength (new_arrivals)) = n_pre)) (PreH16 : ((Zlength (latest)) = n_pre)) (PreH17 : ((Zlength (counts)) = n_pre)) (PreH18 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (new_dist) (0))) /\ ((Znth (edge) (new_dist) (0)) <= 100)))) (PreH19 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (new_arrivals) (0)))) /\ ((Znth (station) (new_arrivals) (0)) <= 200000)))) (PreH20 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals )) (PreH21 : (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos )) (PreH22 : (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos i )) ,
  (IntArray.full arr_pre n_pre new_arrivals )
  **  (IntArray.full d_pre (n_pre - 1 ) new_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ (i < n_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < (n_pre - 1 )) ” 
  &&  “ (0 < best) ” 
  &&  “ (best <= m_pre) ” 
  &&  “ ((pos + 1 ) <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ ((Zlength (old_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (new_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (old_arrivals)) = n_pre) ” 
  &&  “ ((Zlength (new_arrivals)) = n_pre) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (new_dist) (0))) /\ ((Znth (edge) (new_dist) (0)) <= 100))) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (new_arrivals) (0)))) /\ ((Znth (station) (new_arrivals) (0)) <= 200000))) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals ) ” 
  &&  “ (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos ) ” 
  &&  “ (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos i ) ”
  &&  (((arr_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i arr_pre i 0 n_pre new_arrivals )
  **  (IntArray.full d_pre (n_pre - 1 ) new_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
.

Definition solve_partial_solve_wit_26 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (new_arrivals: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (old_dist: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= pos)) (PreH6 : (pos < (n_pre - 1 ))) (PreH7 : (0 < best)) (PreH8 : (best <= m_pre)) (PreH9 : ((pos + 1 ) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH12 : ((Zlength (old_dist)) = (n_pre - 1 ))) (PreH13 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (old_arrivals)) = n_pre)) (PreH15 : ((Zlength (new_arrivals)) = n_pre)) (PreH16 : ((Zlength (latest)) = n_pre)) (PreH17 : ((Zlength (counts)) = n_pre)) (PreH18 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (new_dist) (0))) /\ ((Znth (edge) (new_dist) (0)) <= 100)))) (PreH19 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (new_arrivals) (0)))) /\ ((Znth (station) (new_arrivals) (0)) <= 200000)))) (PreH20 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals )) (PreH21 : (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos )) (PreH22 : (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos i )) ,
  (IntArray.full arr_pre n_pre (replace_Znth (i) (((Znth i new_arrivals 0) - 1 )) (new_arrivals)) )
  **  (IntArray.full d_pre (n_pre - 1 ) new_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ (i < n_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < (n_pre - 1 )) ” 
  &&  “ (0 < best) ” 
  &&  “ (best <= m_pre) ” 
  &&  “ ((pos + 1 ) <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ ((Zlength (old_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (new_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (old_arrivals)) = n_pre) ” 
  &&  “ ((Zlength (new_arrivals)) = n_pre) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (new_dist) (0))) /\ ((Znth (edge) (new_dist) (0)) <= 100))) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (new_arrivals) (0)))) /\ ((Znth (station) (new_arrivals) (0)) <= 200000))) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals ) ” 
  &&  “ (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos ) ” 
  &&  “ (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos i ) ”
  &&  (((arr_pre + (i * sizeof(INT)))) # Int  |-> (Znth i (replace_Znth (i) (((Znth i new_arrivals 0) - 1 )) (new_arrivals)) 0))
  **  (IntArray.missing_i arr_pre i 0 n_pre (replace_Znth (i) (((Znth i new_arrivals 0) - 1 )) (new_arrivals)) )
  **  (IntArray.full d_pre (n_pre - 1 ) new_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
.

Definition solve_partial_solve_wit_27 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (new_arrivals: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (old_dist: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= pos)) (PreH6 : (pos < (n_pre - 1 ))) (PreH7 : (0 < best)) (PreH8 : (best <= m_pre)) (PreH9 : ((pos + 1 ) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH12 : ((Zlength (old_dist)) = (n_pre - 1 ))) (PreH13 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (old_arrivals)) = n_pre)) (PreH15 : ((Zlength (new_arrivals)) = n_pre)) (PreH16 : ((Zlength (latest)) = n_pre)) (PreH17 : ((Zlength (counts)) = n_pre)) (PreH18 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (new_dist) (0))) /\ ((Znth (edge) (new_dist) (0)) <= 100)))) (PreH19 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (new_arrivals) (0)))) /\ ((Znth (station) (new_arrivals) (0)) <= 200000)))) (PreH20 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals )) (PreH21 : (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos )) (PreH22 : (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos i )) ,
  (IntArray.full arr_pre n_pre (replace_Znth (i) (((Znth i new_arrivals 0) - 1 )) (new_arrivals)) )
  **  (IntArray.full d_pre (n_pre - 1 ) new_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ (i < n_pre) ” 
  &&  “ (0 < k) ” 
  &&  “ (k <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos < (n_pre - 1 )) ” 
  &&  “ (0 < best) ” 
  &&  “ (best <= m_pre) ” 
  &&  “ ((pos + 1 ) <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ ((Zlength (old_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (new_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (old_arrivals)) = n_pre) ” 
  &&  “ ((Zlength (new_arrivals)) = n_pre) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (new_dist) (0))) /\ ((Znth (edge) (new_dist) (0)) <= 100))) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (new_arrivals) (0)))) /\ ((Znth (station) (new_arrivals) (0)) <= 200000))) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals ) ” 
  &&  “ (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos ) ” 
  &&  “ (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos i ) ”
  &&  (((late_pre + (i * sizeof(INT)))) # Int  |-> (Znth i latest 0))
  **  (IntArray.missing_i late_pre i 0 n_pre latest )
  **  (IntArray.full arr_pre n_pre (replace_Znth (i) (((Znth i new_arrivals 0) - 1 )) (new_arrivals)) )
  **  (IntArray.full d_pre (n_pre - 1 ) new_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full off_pre n_pre counts )
.

Definition solve_partial_solve_wit_28 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH21 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH22 : ((Zlength (arrivals)) = n_pre)) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals) (0))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH24 : forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))) (PreH25 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ (0 <= ((Znth (i) (destinations) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (destinations) (0)) - 1 ) < n_pre) ” 
  &&  “ (ans <= INT_MAX) ” 
  &&  “ (k <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (ans >= INT_MIN) ” 
  &&  “ (k >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= (i * 200000 )) ” 
  &&  “ (ans <= 2000000000) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals ) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals) (0))) /\ ((Znth (station) (arrivals) (0)) <= 200000))) ” 
  &&  “ forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre))) ” 
  &&  “ (TravelSumPrefix m_pre times destinations arrivals i ans ) ”
  &&  (((b_pre + (i * sizeof(INT)))) # Int  |-> (Znth i destinations 0))
  **  (IntArray.missing_i b_pre i 0 m_pre destinations )
  **  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
.

Definition solve_partial_solve_wit_29 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH21 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH22 : ((Zlength (arrivals)) = n_pre)) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals) (0))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH24 : forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))) (PreH25 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
  **  (IntArray.full arr_pre n_pre arrivals )
|--
  “ (0 <= ((Znth (i) (destinations) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (destinations) (0)) - 1 ) < n_pre) ” 
  &&  “ (ans <= INT_MAX) ” 
  &&  “ (k <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (ans >= INT_MIN) ” 
  &&  “ (k >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= (i * 200000 )) ” 
  &&  “ (ans <= 2000000000) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals ) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals) (0))) /\ ((Znth (station) (arrivals) (0)) <= 200000))) ” 
  &&  “ forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre))) ” 
  &&  “ (TravelSumPrefix m_pre times destinations arrivals i ans ) ”
  &&  (((arr_pre + (((Znth i destinations 0) - 1 ) * sizeof(INT)))) # Int  |-> (Znth ((Znth i destinations 0) - 1 ) arrivals 0))
  **  (IntArray.missing_i arr_pre ((Znth i destinations 0) - 1 ) 0 n_pre arrivals )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
.

Definition solve_partial_solve_wit_30 := 
forall (arr_pre: Z) (off_pre: Z) (late_pre: Z) (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (SightseeingInputsBounded n_pre m_pre dist times origins destinations )) (PreH21 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH22 : ((Zlength (arrivals)) = n_pre)) (PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals) (0))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) (PreH24 : forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))) (PreH25 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  (IntArray.full arr_pre n_pre arrivals )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
|--
  “ (0 <= ((Znth (i) (destinations) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (destinations) (0)) - 1 ) < n_pre) ” 
  &&  “ (ans <= INT_MAX) ” 
  &&  “ (k <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (ans >= INT_MIN) ” 
  &&  “ (k >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (0 <= ans) ” 
  &&  “ (ans <= (i * 200000 )) ” 
  &&  “ (ans <= 2000000000) ” 
  &&  “ (SightseeingInputsBounded n_pre m_pre dist times origins destinations ) ” 
  &&  “ (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals ) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals) (0))) /\ ((Znth (station) (arrivals) (0)) <= 200000))) ” 
  &&  “ forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre))) ” 
  &&  “ (TravelSumPrefix m_pre times destinations arrivals i ans ) ”
  &&  (((t_pre + (i * sizeof(INT)))) # Int  |-> (Znth i times 0))
  **  (IntArray.missing_i t_pre i 0 m_pre times )
  **  (IntArray.full arr_pre n_pre arrivals )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full late_pre n_pre latest )
  **  (IntArray.full off_pre n_pre counts )
.

Module Type VC_Correct.


Axiom proof_of_solve_safety_wit_1 : solve_safety_wit_1.
Axiom proof_of_solve_safety_wit_2 : solve_safety_wit_2.
Axiom proof_of_solve_safety_wit_3 : solve_safety_wit_3.
Axiom proof_of_solve_safety_wit_4 : solve_safety_wit_4.
Axiom proof_of_solve_safety_wit_5 : solve_safety_wit_5.
Axiom proof_of_solve_safety_wit_6 : solve_safety_wit_6.
Axiom proof_of_solve_safety_wit_7 : solve_safety_wit_7.
Axiom proof_of_solve_safety_wit_8 : solve_safety_wit_8.
Axiom proof_of_solve_safety_wit_9 : solve_safety_wit_9.
Axiom proof_of_solve_safety_wit_10 : solve_safety_wit_10.
Axiom proof_of_solve_safety_wit_11 : solve_safety_wit_11.
Axiom proof_of_solve_safety_wit_12 : solve_safety_wit_12.
Axiom proof_of_solve_safety_wit_13 : solve_safety_wit_13.
Axiom proof_of_solve_safety_wit_14 : solve_safety_wit_14.
Axiom proof_of_solve_safety_wit_15 : solve_safety_wit_15.
Axiom proof_of_solve_safety_wit_16 : solve_safety_wit_16.
Axiom proof_of_solve_safety_wit_17 : solve_safety_wit_17.
Axiom proof_of_solve_safety_wit_18 : solve_safety_wit_18.
Axiom proof_of_solve_safety_wit_19 : solve_safety_wit_19.
Axiom proof_of_solve_safety_wit_20 : solve_safety_wit_20.
Axiom proof_of_solve_safety_wit_21 : solve_safety_wit_21.
Axiom proof_of_solve_safety_wit_22 : solve_safety_wit_22.
Axiom proof_of_solve_safety_wit_23 : solve_safety_wit_23.
Axiom proof_of_solve_safety_wit_24 : solve_safety_wit_24.
Axiom proof_of_solve_safety_wit_25 : solve_safety_wit_25.
Axiom proof_of_solve_safety_wit_26 : solve_safety_wit_26.
Axiom proof_of_solve_safety_wit_27 : solve_safety_wit_27.
Axiom proof_of_solve_safety_wit_28 : solve_safety_wit_28.
Axiom proof_of_solve_safety_wit_29 : solve_safety_wit_29.
Axiom proof_of_solve_safety_wit_30 : solve_safety_wit_30.
Axiom proof_of_solve_safety_wit_31 : solve_safety_wit_31.
Axiom proof_of_solve_safety_wit_32 : solve_safety_wit_32.
Axiom proof_of_solve_safety_wit_33 : solve_safety_wit_33.
Axiom proof_of_solve_safety_wit_34 : solve_safety_wit_34.
Axiom proof_of_solve_safety_wit_35 : solve_safety_wit_35.
Axiom proof_of_solve_safety_wit_36 : solve_safety_wit_36.
Axiom proof_of_solve_safety_wit_37 : solve_safety_wit_37.
Axiom proof_of_solve_safety_wit_38 : solve_safety_wit_38.
Axiom proof_of_solve_safety_wit_39 : solve_safety_wit_39.
Axiom proof_of_solve_safety_wit_40 : solve_safety_wit_40.
Axiom proof_of_solve_safety_wit_41 : solve_safety_wit_41.
Axiom proof_of_solve_safety_wit_42 : solve_safety_wit_42.
Axiom proof_of_solve_safety_wit_43 : solve_safety_wit_43.
Axiom proof_of_solve_safety_wit_44 : solve_safety_wit_44.
Axiom proof_of_solve_safety_wit_45 : solve_safety_wit_45.
Axiom proof_of_solve_safety_wit_46 : solve_safety_wit_46.
Axiom proof_of_solve_safety_wit_47 : solve_safety_wit_47.
Axiom proof_of_solve_safety_wit_48 : solve_safety_wit_48.
Axiom proof_of_solve_safety_wit_49 : solve_safety_wit_49.
Axiom proof_of_solve_safety_wit_50 : solve_safety_wit_50.
Axiom proof_of_solve_safety_wit_51 : solve_safety_wit_51.
Axiom proof_of_solve_safety_wit_52 : solve_safety_wit_52.
Axiom proof_of_solve_safety_wit_53 : solve_safety_wit_53.
Axiom proof_of_solve_safety_wit_54 : solve_safety_wit_54.
Axiom proof_of_solve_safety_wit_55 : solve_safety_wit_55.
Axiom proof_of_solve_safety_wit_56 : solve_safety_wit_56.
Axiom proof_of_solve_safety_wit_57 : solve_safety_wit_57.
Axiom proof_of_solve_safety_wit_58 : solve_safety_wit_58.
Axiom proof_of_solve_safety_wit_59 : solve_safety_wit_59.
Axiom proof_of_solve_safety_wit_60 : solve_safety_wit_60.
Axiom proof_of_solve_safety_wit_61 : solve_safety_wit_61.
Axiom proof_of_solve_safety_wit_62 : solve_safety_wit_62.
Axiom proof_of_solve_safety_wit_63 : solve_safety_wit_63.
Axiom proof_of_solve_safety_wit_64 : solve_safety_wit_64.
Axiom proof_of_solve_safety_wit_65 : solve_safety_wit_65.
Axiom proof_of_solve_entail_wit_1 : solve_entail_wit_1.
Axiom proof_of_solve_entail_wit_2 : solve_entail_wit_2.
Axiom proof_of_solve_entail_wit_3 : solve_entail_wit_3.
Axiom proof_of_solve_entail_wit_4 : solve_entail_wit_4.
Axiom proof_of_solve_entail_wit_5 : solve_entail_wit_5.
Axiom proof_of_solve_entail_wit_6 : solve_entail_wit_6.
Axiom proof_of_solve_entail_wit_7_1 : solve_entail_wit_7_1.
Axiom proof_of_solve_entail_wit_7_2 : solve_entail_wit_7_2.
Axiom proof_of_solve_entail_wit_8 : solve_entail_wit_8.
Axiom proof_of_solve_entail_wit_9 : solve_entail_wit_9.
Axiom proof_of_solve_entail_wit_10_1 : solve_entail_wit_10_1.
Axiom proof_of_solve_entail_wit_10_2 : solve_entail_wit_10_2.
Axiom proof_of_solve_entail_wit_10_3 : solve_entail_wit_10_3.
Axiom proof_of_solve_entail_wit_10_4 : solve_entail_wit_10_4.
Axiom proof_of_solve_entail_wit_11 : solve_entail_wit_11.
Axiom proof_of_solve_entail_wit_12 : solve_entail_wit_12.
Axiom proof_of_solve_entail_wit_13 : solve_entail_wit_13.
Axiom proof_of_solve_entail_wit_14 : solve_entail_wit_14.
Axiom proof_of_solve_entail_wit_15 : solve_entail_wit_15.
Axiom proof_of_solve_entail_wit_16_1 : solve_entail_wit_16_1.
Axiom proof_of_solve_entail_wit_16_2 : solve_entail_wit_16_2.
Axiom proof_of_solve_entail_wit_17_1 : solve_entail_wit_17_1.
Axiom proof_of_solve_entail_wit_17_2 : solve_entail_wit_17_2.
Axiom proof_of_solve_entail_wit_17_3 : solve_entail_wit_17_3.
Axiom proof_of_solve_entail_wit_18 : solve_entail_wit_18.
Axiom proof_of_solve_entail_wit_19 : solve_entail_wit_19.
Axiom proof_of_solve_entail_wit_20_1 : solve_entail_wit_20_1.
Axiom proof_of_solve_entail_wit_20_2 : solve_entail_wit_20_2.
Axiom proof_of_solve_entail_wit_21 : solve_entail_wit_21.
Axiom proof_of_solve_entail_wit_22 : solve_entail_wit_22.
Axiom proof_of_solve_entail_wit_23_1 : solve_entail_wit_23_1.
Axiom proof_of_solve_entail_wit_23_2 : solve_entail_wit_23_2.
Axiom proof_of_solve_entail_wit_23_3 : solve_entail_wit_23_3.
Axiom proof_of_solve_entail_wit_24 : solve_entail_wit_24.
Axiom proof_of_solve_entail_wit_25 : solve_entail_wit_25.
Axiom proof_of_solve_return_wit_1 : solve_return_wit_1.
Axiom proof_of_solve_partial_solve_wit_1 : solve_partial_solve_wit_1.
Axiom proof_of_solve_partial_solve_wit_2 : solve_partial_solve_wit_2.
Axiom proof_of_solve_partial_solve_wit_3 : solve_partial_solve_wit_3.
Axiom proof_of_solve_partial_solve_wit_4 : solve_partial_solve_wit_4.
Axiom proof_of_solve_partial_solve_wit_5 : solve_partial_solve_wit_5.
Axiom proof_of_solve_partial_solve_wit_6 : solve_partial_solve_wit_6.
Axiom proof_of_solve_partial_solve_wit_7 : solve_partial_solve_wit_7.
Axiom proof_of_solve_partial_solve_wit_8 : solve_partial_solve_wit_8.
Axiom proof_of_solve_partial_solve_wit_9 : solve_partial_solve_wit_9.
Axiom proof_of_solve_partial_solve_wit_10 : solve_partial_solve_wit_10.
Axiom proof_of_solve_partial_solve_wit_11 : solve_partial_solve_wit_11.
Axiom proof_of_solve_partial_solve_wit_12 : solve_partial_solve_wit_12.
Axiom proof_of_solve_partial_solve_wit_13 : solve_partial_solve_wit_13.
Axiom proof_of_solve_partial_solve_wit_14 : solve_partial_solve_wit_14.
Axiom proof_of_solve_partial_solve_wit_15 : solve_partial_solve_wit_15.
Axiom proof_of_solve_partial_solve_wit_16 : solve_partial_solve_wit_16.
Axiom proof_of_solve_partial_solve_wit_17 : solve_partial_solve_wit_17.
Axiom proof_of_solve_partial_solve_wit_18 : solve_partial_solve_wit_18.
Axiom proof_of_solve_partial_solve_wit_19 : solve_partial_solve_wit_19.
Axiom proof_of_solve_partial_solve_wit_20 : solve_partial_solve_wit_20.
Axiom proof_of_solve_partial_solve_wit_21 : solve_partial_solve_wit_21.
Axiom proof_of_solve_partial_solve_wit_22 : solve_partial_solve_wit_22.
Axiom proof_of_solve_partial_solve_wit_23 : solve_partial_solve_wit_23.
Axiom proof_of_solve_partial_solve_wit_24 : solve_partial_solve_wit_24.
Axiom proof_of_solve_partial_solve_wit_25 : solve_partial_solve_wit_25.
Axiom proof_of_solve_partial_solve_wit_26 : solve_partial_solve_wit_26.
Axiom proof_of_solve_partial_solve_wit_27 : solve_partial_solve_wit_27.
Axiom proof_of_solve_partial_solve_wit_28 : solve_partial_solve_wit_28.
Axiom proof_of_solve_partial_solve_wit_29 : solve_partial_solve_wit_29.
Axiom proof_of_solve_partial_solve_wit_30 : solve_partial_solve_wit_30.

End VC_Correct.
