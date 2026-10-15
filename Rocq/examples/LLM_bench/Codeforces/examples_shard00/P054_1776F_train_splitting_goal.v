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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P054_1776F_train_splitting_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval <> 0)) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : ((n_pre - 1 ) <= (Zlength (e)))) (PreH5 : ((Zlength (e)) <= 1225)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (e)))) -> (((0 <= (fst ((Znth i e __default__Prod_Z_Z)))) /\ ((fst ((Znth i e __default__Prod_Z_Z))) < n_pre)) /\ ((0 <= (snd ((Znth i e __default__Prod_Z_Z)))) /\ ((snd ((Znth i e __default__Prod_Z_Z))) < n_pre))))) (PreH7 : (Pre n_pre e )) (PreH8 : (m_pre = (Zlength (e)))) (PreH9 : ((Zlength (u_data)) = m_pre)) (PreH10 : ((Zlength (v_data)) = m_pre)) (PreH11 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((Znth i_2 u_data 0) = (fst ((Znth i_2 e __default__Prod_Z_Z)))) /\ ((Znth i_2 v_data 0) = (snd ((Znth i_2 e __default__Prod_Z_Z))))))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.full retval n_pre (repeat_Z (0) (n_pre)) )
  **  ((( &( "deg" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees: (@list Z)) (i: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (DegreePrefix n_pre e i degrees )) (PreH15 : forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees 0)) /\ ((Znth x degrees 0) <= (2 * i ))))) ,
  (IntArray.full deg n_pre degrees )
  **  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
|--
  “ (((Znth (Znth i u_data 0) degrees 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (Znth i u_data 0) degrees 0) + 1 )) ”
.

Definition solver_safety_wit_3 := 
(
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees: (@list Z)) (i: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (DegreePrefix n_pre e i degrees )) (PreH15 : forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees 0)) /\ ((Znth x degrees 0) <= (2 * i ))))) ,
  (IntArray.full deg n_pre (replace_Znth ((Znth i u_data 0)) (((Znth (Znth i u_data 0) degrees 0) + 1 )) (degrees)) )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_full colors_pre m_pre )
|--
  “ (((Znth (Znth i v_data 0) (replace_Znth ((Znth i u_data 0)) (((Znth (Znth i u_data 0) degrees 0) + 1 )) (degrees)) 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (Znth i v_data 0) (replace_Znth ((Znth i u_data 0)) (((Znth (Znth i u_data 0) degrees 0) + 1 )) (degrees)) 0) + 1 )) ”
) \/
(
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees: (@list Z)) (i: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (DegreePrefix n_pre e i degrees )) (PreH15 : forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees 0)) /\ ((Znth x degrees 0) <= (2 * i ))))) ,
  (IntArray.full deg n_pre (replace_Znth ((Znth i u_data 0)) (((Znth (Znth i u_data 0) degrees 0) + 1 )) (degrees)) )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_full colors_pre m_pre )
|--
  “ (((Znth (Znth i v_data 0) (replace_Znth ((Znth i u_data 0)) (((Znth (Znth i u_data 0) degrees 0) + 1 )) (degrees)) 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (Znth i v_data 0) (replace_Znth ((Znth i u_data 0)) (((Znth (Znth i u_data 0) degrees 0) + 1 )) (degrees)) 0) + 1 )) ”
).

Definition solver_safety_wit_3_split_goal_1 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees: (@list Z)) (i: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (DegreePrefix n_pre e i degrees )) (PreH15 : forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees 0)) /\ ((Znth x degrees 0) <= (2 * i ))))) ,
  (IntArray.full deg n_pre (replace_Znth ((Znth i u_data 0)) (((Znth (Znth i u_data 0) degrees 0) + 1 )) (degrees)) )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_full colors_pre m_pre )
|--
  “ (((Znth (Znth i v_data 0) (replace_Znth ((Znth i u_data 0)) (((Znth (Znth i u_data 0) degrees 0) + 1 )) (degrees)) 0) + 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_3_split_goal_2 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees: (@list Z)) (i: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (DegreePrefix n_pre e i degrees )) (PreH15 : forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees 0)) /\ ((Znth x degrees 0) <= (2 * i ))))) ,
  (IntArray.full deg n_pre (replace_Znth ((Znth i u_data 0)) (((Znth (Znth i u_data 0) degrees 0) + 1 )) (degrees)) )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_full colors_pre m_pre )
|--
  “ ((INT_MIN) <= ((Znth (Znth i v_data 0) (replace_Znth ((Znth i u_data 0)) (((Znth (Znth i u_data 0) degrees 0) + 1 )) (degrees)) 0) + 1 )) ”
.

Definition solver_safety_wit_4 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees: (@list Z)) (i: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (DegreePrefix n_pre e i degrees )) (PreH15 : forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees 0)) /\ ((Znth x degrees 0) <= (2 * i ))))) ,
  (IntArray.full deg n_pre (replace_Znth ((Znth i v_data 0)) (((Znth (Znth i v_data 0) (replace_Znth ((Znth i u_data 0)) (((Znth (Znth i u_data 0) degrees 0) + 1 )) (degrees)) 0) + 1 )) ((replace_Znth ((Znth i u_data 0)) (((Znth (Znth i u_data 0) degrees 0) + 1 )) (degrees)))) )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_full colors_pre m_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_5 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees: (@list Z)) (i: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i >= m_pre)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (DegreePrefix n_pre e i degrees )) (PreH15 : forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees 0)) /\ ((Znth x degrees 0) <= (2 * i ))))) ,
  ((( &( "pivot" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_6 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees: (@list Z)) (i: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i >= m_pre)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (DegreePrefix n_pre e i degrees )) (PreH15 : forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees 0)) /\ ((Znth x degrees 0) <= (2 * i ))))) ,
  ((( &( "pivot" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_7 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees: (@list Z)) (i: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i >= m_pre)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (DegreePrefix n_pre e i degrees )) (PreH15 : forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees 0)) /\ ((Znth x degrees 0) <= (2 * i ))))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "pivot" ) )) # Int  |-> (-1))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_8 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees: (@list Z)) (i: Z) (pivot: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (deg <> 0)) (PreH3 : (pivot = (-1))) (PreH4 : (3 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : ((n_pre - 1 ) <= m_pre)) (PreH7 : (m_pre <= 1225)) (PreH8 : (m_pre = (Zlength (e)))) (PreH9 : ((Zlength (u_data)) = m_pre)) (PreH10 : ((Zlength (v_data)) = m_pre)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH12 : (Pre n_pre e )) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (DegreePrefix n_pre e m_pre degrees )) (PreH16 : (PivotPrefix n_pre degrees i )) (PreH17 : forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees 0)) /\ ((Znth x degrees 0) <= (n_pre - 1 ))))) ,
  (IntArray.full deg n_pre degrees )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition solver_safety_wit_9 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees: (@list Z)) (i: Z) (pivot: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (deg <> 0)) (PreH3 : (pivot = (-1))) (PreH4 : (3 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : ((n_pre - 1 ) <= m_pre)) (PreH7 : (m_pre <= 1225)) (PreH8 : (m_pre = (Zlength (e)))) (PreH9 : ((Zlength (u_data)) = m_pre)) (PreH10 : ((Zlength (v_data)) = m_pre)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH12 : (Pre n_pre e )) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (DegreePrefix n_pre e m_pre degrees )) (PreH16 : (PivotPrefix n_pre degrees i )) (PreH17 : forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees 0)) /\ ((Znth x degrees 0) <= (n_pre - 1 ))))) ,
  (IntArray.full deg n_pre degrees )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_10 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees: (@list Z)) (i: Z) (pivot: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i degrees 0) >= (n_pre - 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (deg <> 0)) (PreH4 : (pivot = (-1))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : ((n_pre - 1 ) <= m_pre)) (PreH8 : (m_pre <= 1225)) (PreH9 : (m_pre = (Zlength (e)))) (PreH10 : ((Zlength (u_data)) = m_pre)) (PreH11 : ((Zlength (v_data)) = m_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH13 : (Pre n_pre e )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (DegreePrefix n_pre e m_pre degrees )) (PreH17 : (PivotPrefix n_pre degrees i )) (PreH18 : forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees 0)) /\ ((Znth x degrees 0) <= (n_pre - 1 ))))) ,
  (IntArray.full deg n_pre degrees )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_11 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees: (@list Z)) (deg: Z) (pivot: Z)  __default__Prod_Z_Z (PreH1 : (deg <> 0)) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : ((n_pre - 1 ) <= m_pre)) (PreH5 : (m_pre <= 1225)) (PreH6 : (m_pre = (Zlength (e)))) (PreH7 : ((Zlength (u_data)) = m_pre)) (PreH8 : ((Zlength (v_data)) = m_pre)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH10 : (Pre n_pre e )) (PreH11 : (DegreePrefix n_pre e m_pre degrees )) (PreH12 : (PivotChoice n_pre degrees pivot )) ,
  ((( &( "kinds" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_12 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees: (@list Z)) (deg: Z) (pivot: Z)  __default__Prod_Z_Z (PreH1 : (pivot >= 0)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (DegreePrefix n_pre e m_pre degrees )) (PreH13 : (PivotChoice n_pre degrees pivot )) ,
  ((( &( "kinds" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_13 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees: (@list Z)) (deg: Z) (pivot: Z)  __default__Prod_Z_Z (PreH1 : (pivot >= 0)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (DegreePrefix n_pre e m_pre degrees )) (PreH13 : (PivotChoice n_pre degrees pivot )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "kinds" ) )) # Int  |-> 2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_14 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i v_data 0) = pivot)) (PreH2 : ((Znth i u_data 0) <> pivot)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 2)) (PreH6 : (0 <= pivot)) (PreH7 : (pivot < n_pre)) (PreH8 : (3 <= n_pre)) (PreH9 : (n_pre <= 50)) (PreH10 : ((n_pre - 1 ) <= m_pre)) (PreH11 : (m_pre <= 1225)) (PreH12 : (m_pre = (Zlength (e)))) (PreH13 : ((Zlength (u_data)) = m_pre)) (PreH14 : ((Zlength (v_data)) = m_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH16 : (Pre n_pre e )) (PreH17 : (DegreePrefix n_pre e m_pre degrees )) (PreH18 : (PivotChoice n_pre degrees pivot )) (PreH19 : (0 <= i)) (PreH20 : (i <= m_pre)) (PreH21 : (PivotColorPrefix e pivot i labels )) ,
  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "kinds" ) )) # Int  |-> kinds)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_15 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i u_data 0) = pivot)) (PreH2 : (i < m_pre)) (PreH3 : (deg <> 0)) (PreH4 : (kinds = 2)) (PreH5 : (0 <= pivot)) (PreH6 : (pivot < n_pre)) (PreH7 : (3 <= n_pre)) (PreH8 : (n_pre <= 50)) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (m_pre <= 1225)) (PreH11 : (m_pre = (Zlength (e)))) (PreH12 : ((Zlength (u_data)) = m_pre)) (PreH13 : ((Zlength (v_data)) = m_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH15 : (Pre n_pre e )) (PreH16 : (DegreePrefix n_pre e m_pre degrees )) (PreH17 : (PivotChoice n_pre degrees pivot )) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : (PivotColorPrefix e pivot i labels )) ,
  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "kinds" ) )) # Int  |-> kinds)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_16 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i v_data 0) <> pivot)) (PreH2 : ((Znth i u_data 0) <> pivot)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 2)) (PreH6 : (0 <= pivot)) (PreH7 : (pivot < n_pre)) (PreH8 : (3 <= n_pre)) (PreH9 : (n_pre <= 50)) (PreH10 : ((n_pre - 1 ) <= m_pre)) (PreH11 : (m_pre <= 1225)) (PreH12 : (m_pre = (Zlength (e)))) (PreH13 : ((Zlength (u_data)) = m_pre)) (PreH14 : ((Zlength (v_data)) = m_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH16 : (Pre n_pre e )) (PreH17 : (DegreePrefix n_pre e m_pre degrees )) (PreH18 : (PivotChoice n_pre degrees pivot )) (PreH19 : (0 <= i)) (PreH20 : (i <= m_pre)) (PreH21 : (PivotColorPrefix e pivot i labels )) ,
  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "kinds" ) )) # Int  |-> kinds)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_17 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i v_data 0) = pivot)) (PreH2 : ((Znth i u_data 0) <> pivot)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 2)) (PreH6 : (0 <= pivot)) (PreH7 : (pivot < n_pre)) (PreH8 : (3 <= n_pre)) (PreH9 : (n_pre <= 50)) (PreH10 : ((n_pre - 1 ) <= m_pre)) (PreH11 : (m_pre <= 1225)) (PreH12 : (m_pre = (Zlength (e)))) (PreH13 : ((Zlength (u_data)) = m_pre)) (PreH14 : ((Zlength (v_data)) = m_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH16 : (Pre n_pre e )) (PreH17 : (DegreePrefix n_pre e m_pre degrees )) (PreH18 : (PivotChoice n_pre degrees pivot )) (PreH19 : (0 <= i)) (PreH20 : (i <= m_pre)) (PreH21 : (PivotColorPrefix e pivot i labels )) ,
  (IntArray.seg colors_pre 0 (i + 1 ) (app (labels) ((cons (1) ((@nil Z))))) )
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "kinds" ) )) # Int  |-> kinds)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full deg n_pre degrees )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_18 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i u_data 0) = pivot)) (PreH2 : (i < m_pre)) (PreH3 : (deg <> 0)) (PreH4 : (kinds = 2)) (PreH5 : (0 <= pivot)) (PreH6 : (pivot < n_pre)) (PreH7 : (3 <= n_pre)) (PreH8 : (n_pre <= 50)) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (m_pre <= 1225)) (PreH11 : (m_pre = (Zlength (e)))) (PreH12 : ((Zlength (u_data)) = m_pre)) (PreH13 : ((Zlength (v_data)) = m_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH15 : (Pre n_pre e )) (PreH16 : (DegreePrefix n_pre e m_pre degrees )) (PreH17 : (PivotChoice n_pre degrees pivot )) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : (PivotColorPrefix e pivot i labels )) ,
  (IntArray.seg colors_pre 0 (i + 1 ) (app (labels) ((cons (1) ((@nil Z))))) )
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "kinds" ) )) # Int  |-> kinds)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full deg n_pre degrees )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_19 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i v_data 0) <> pivot)) (PreH2 : ((Znth i u_data 0) <> pivot)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 2)) (PreH6 : (0 <= pivot)) (PreH7 : (pivot < n_pre)) (PreH8 : (3 <= n_pre)) (PreH9 : (n_pre <= 50)) (PreH10 : ((n_pre - 1 ) <= m_pre)) (PreH11 : (m_pre <= 1225)) (PreH12 : (m_pre = (Zlength (e)))) (PreH13 : ((Zlength (u_data)) = m_pre)) (PreH14 : ((Zlength (v_data)) = m_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH16 : (Pre n_pre e )) (PreH17 : (DegreePrefix n_pre e m_pre degrees )) (PreH18 : (PivotChoice n_pre degrees pivot )) (PreH19 : (0 <= i)) (PreH20 : (i <= m_pre)) (PreH21 : (PivotColorPrefix e pivot i labels )) ,
  (IntArray.seg colors_pre 0 (i + 1 ) (app (labels) ((cons (2) ((@nil Z))))) )
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "kinds" ) )) # Int  |-> kinds)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full deg n_pre degrees )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_20 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees: (@list Z)) (deg: Z) (pivot: Z)  __default__Prod_Z_Z (PreH1 : (pivot < 0)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (DegreePrefix n_pre e m_pre degrees )) (PreH13 : (PivotChoice n_pre degrees pivot )) ,
  ((( &( "kinds" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition solver_safety_wit_21 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees: (@list Z)) (deg: Z) (pivot: Z)  __default__Prod_Z_Z (PreH1 : (pivot < 0)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (DegreePrefix n_pre e m_pre degrees )) (PreH13 : (PivotChoice n_pre degrees pivot )) ,
  ((( &( "first" ) )) # Int  |->_)
  **  ((( &( "kinds" ) )) # Int  |-> 3)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_22 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees: (@list Z)) (deg: Z) (pivot: Z)  __default__Prod_Z_Z (PreH1 : (pivot < 0)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (DegreePrefix n_pre e m_pre degrees )) (PreH13 : (PivotChoice n_pre degrees pivot )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "first" ) )) # Int  |-> 1)
  **  ((( &( "kinds" ) )) # Int  |-> 3)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_23 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (deg <> 0)) (PreH3 : (kinds = 3)) (PreH4 : (pivot = (-1))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : ((n_pre - 1 ) <= m_pre)) (PreH8 : (m_pre <= 1225)) (PreH9 : (m_pre = (Zlength (e)))) (PreH10 : ((Zlength (u_data)) = m_pre)) (PreH11 : ((Zlength (v_data)) = m_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH13 : (Pre n_pre e )) (PreH14 : (DegreePrefix n_pre e m_pre degrees )) (PreH15 : (PivotChoice n_pre degrees pivot )) (PreH16 : (0 <= i)) (PreH17 : (i <= m_pre)) (PreH18 : (first = 1)) (PreH19 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "kinds" ) )) # Int  |-> kinds)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_24 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (deg <> 0)) (PreH3 : (kinds = 3)) (PreH4 : (pivot = (-1))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : ((n_pre - 1 ) <= m_pre)) (PreH8 : (m_pre <= 1225)) (PreH9 : (m_pre = (Zlength (e)))) (PreH10 : ((Zlength (u_data)) = m_pre)) (PreH11 : ((Zlength (v_data)) = m_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH13 : (Pre n_pre e )) (PreH14 : (DegreePrefix n_pre e m_pre degrees )) (PreH15 : (PivotChoice n_pre degrees pivot )) (PreH16 : (0 <= i)) (PreH17 : (i <= m_pre)) (PreH18 : (first = 0)) (PreH19 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "kinds" ) )) # Int  |-> kinds)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_25 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i u_data 0) <> 0)) (PreH2 : (i < m_pre)) (PreH3 : (deg <> 0)) (PreH4 : (kinds = 3)) (PreH5 : (pivot = (-1))) (PreH6 : (3 <= n_pre)) (PreH7 : (n_pre <= 50)) (PreH8 : ((n_pre - 1 ) <= m_pre)) (PreH9 : (m_pre <= 1225)) (PreH10 : (m_pre = (Zlength (e)))) (PreH11 : ((Zlength (u_data)) = m_pre)) (PreH12 : ((Zlength (v_data)) = m_pre)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH14 : (Pre n_pre e )) (PreH15 : (DegreePrefix n_pre e m_pre degrees )) (PreH16 : (PivotChoice n_pre degrees pivot )) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (first = 0)) (PreH20 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "kinds" ) )) # Int  |-> kinds)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_26 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i u_data 0) <> 0)) (PreH2 : (i < m_pre)) (PreH3 : (deg <> 0)) (PreH4 : (kinds = 3)) (PreH5 : (pivot = (-1))) (PreH6 : (3 <= n_pre)) (PreH7 : (n_pre <= 50)) (PreH8 : ((n_pre - 1 ) <= m_pre)) (PreH9 : (m_pre <= 1225)) (PreH10 : (m_pre = (Zlength (e)))) (PreH11 : ((Zlength (u_data)) = m_pre)) (PreH12 : ((Zlength (v_data)) = m_pre)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH14 : (Pre n_pre e )) (PreH15 : (DegreePrefix n_pre e m_pre degrees )) (PreH16 : (PivotChoice n_pre degrees pivot )) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (first = 1)) (PreH20 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "kinds" ) )) # Int  |-> kinds)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_27 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (first <> 0)) (PreH2 : ((Znth i u_data 0) = 0)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 3)) (PreH6 : (pivot = (-1))) (PreH7 : (3 <= n_pre)) (PreH8 : (n_pre <= 50)) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (m_pre <= 1225)) (PreH11 : (m_pre = (Zlength (e)))) (PreH12 : ((Zlength (u_data)) = m_pre)) (PreH13 : ((Zlength (v_data)) = m_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH15 : (Pre n_pre e )) (PreH16 : (DegreePrefix n_pre e m_pre degrees )) (PreH17 : (PivotChoice n_pre degrees pivot )) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : (first = 0)) (PreH21 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "kinds" ) )) # Int  |-> kinds)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ False ”
.

Definition solver_safety_wit_28 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (first = 0)) (PreH2 : ((Znth i u_data 0) = 0)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 3)) (PreH6 : (pivot = (-1))) (PreH7 : (3 <= n_pre)) (PreH8 : (n_pre <= 50)) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (m_pre <= 1225)) (PreH11 : (m_pre = (Zlength (e)))) (PreH12 : ((Zlength (u_data)) = m_pre)) (PreH13 : ((Zlength (v_data)) = m_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH15 : (Pre n_pre e )) (PreH16 : (DegreePrefix n_pre e m_pre degrees )) (PreH17 : (PivotChoice n_pre degrees pivot )) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : (first = 0)) (PreH21 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "kinds" ) )) # Int  |-> kinds)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_29 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (first <> 0)) (PreH2 : ((Znth i u_data 0) = 0)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 3)) (PreH6 : (pivot = (-1))) (PreH7 : (3 <= n_pre)) (PreH8 : (n_pre <= 50)) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (m_pre <= 1225)) (PreH11 : (m_pre = (Zlength (e)))) (PreH12 : ((Zlength (u_data)) = m_pre)) (PreH13 : ((Zlength (v_data)) = m_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH15 : (Pre n_pre e )) (PreH16 : (DegreePrefix n_pre e m_pre degrees )) (PreH17 : (PivotChoice n_pre degrees pivot )) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : (first = 1)) (PreH21 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "kinds" ) )) # Int  |-> kinds)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_30 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (first = 0)) (PreH2 : ((Znth i u_data 0) = 0)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 3)) (PreH6 : (pivot = (-1))) (PreH7 : (3 <= n_pre)) (PreH8 : (n_pre <= 50)) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (m_pre <= 1225)) (PreH11 : (m_pre = (Zlength (e)))) (PreH12 : ((Zlength (u_data)) = m_pre)) (PreH13 : ((Zlength (v_data)) = m_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH15 : (Pre n_pre e )) (PreH16 : (DegreePrefix n_pre e m_pre degrees )) (PreH17 : (PivotChoice n_pre degrees pivot )) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : (first = 1)) (PreH21 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "kinds" ) )) # Int  |-> kinds)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ False ”
.

Definition solver_safety_wit_31 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (first <> 0)) (PreH2 : ((Znth i v_data 0) = 0)) (PreH3 : ((Znth i u_data 0) <> 0)) (PreH4 : (i < m_pre)) (PreH5 : (deg <> 0)) (PreH6 : (kinds = 3)) (PreH7 : (pivot = (-1))) (PreH8 : (3 <= n_pre)) (PreH9 : (n_pre <= 50)) (PreH10 : ((n_pre - 1 ) <= m_pre)) (PreH11 : (m_pre <= 1225)) (PreH12 : (m_pre = (Zlength (e)))) (PreH13 : ((Zlength (u_data)) = m_pre)) (PreH14 : ((Zlength (v_data)) = m_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH16 : (Pre n_pre e )) (PreH17 : (DegreePrefix n_pre e m_pre degrees )) (PreH18 : (PivotChoice n_pre degrees pivot )) (PreH19 : (0 <= i)) (PreH20 : (i <= m_pre)) (PreH21 : (first = 1)) (PreH22 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "kinds" ) )) # Int  |-> kinds)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_32 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (first = 0)) (PreH2 : ((Znth i v_data 0) = 0)) (PreH3 : ((Znth i u_data 0) <> 0)) (PreH4 : (i < m_pre)) (PreH5 : (deg <> 0)) (PreH6 : (kinds = 3)) (PreH7 : (pivot = (-1))) (PreH8 : (3 <= n_pre)) (PreH9 : (n_pre <= 50)) (PreH10 : ((n_pre - 1 ) <= m_pre)) (PreH11 : (m_pre <= 1225)) (PreH12 : (m_pre = (Zlength (e)))) (PreH13 : ((Zlength (u_data)) = m_pre)) (PreH14 : ((Zlength (v_data)) = m_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH16 : (Pre n_pre e )) (PreH17 : (DegreePrefix n_pre e m_pre degrees )) (PreH18 : (PivotChoice n_pre degrees pivot )) (PreH19 : (0 <= i)) (PreH20 : (i <= m_pre)) (PreH21 : (first = 1)) (PreH22 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "kinds" ) )) # Int  |-> kinds)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ False ”
.

Definition solver_safety_wit_33 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (first <> 0)) (PreH2 : ((Znth i v_data 0) = 0)) (PreH3 : ((Znth i u_data 0) <> 0)) (PreH4 : (i < m_pre)) (PreH5 : (deg <> 0)) (PreH6 : (kinds = 3)) (PreH7 : (pivot = (-1))) (PreH8 : (3 <= n_pre)) (PreH9 : (n_pre <= 50)) (PreH10 : ((n_pre - 1 ) <= m_pre)) (PreH11 : (m_pre <= 1225)) (PreH12 : (m_pre = (Zlength (e)))) (PreH13 : ((Zlength (u_data)) = m_pre)) (PreH14 : ((Zlength (v_data)) = m_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH16 : (Pre n_pre e )) (PreH17 : (DegreePrefix n_pre e m_pre degrees )) (PreH18 : (PivotChoice n_pre degrees pivot )) (PreH19 : (0 <= i)) (PreH20 : (i <= m_pre)) (PreH21 : (first = 0)) (PreH22 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "kinds" ) )) # Int  |-> kinds)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ False ”
.

Definition solver_safety_wit_34 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (first = 0)) (PreH2 : ((Znth i v_data 0) = 0)) (PreH3 : ((Znth i u_data 0) <> 0)) (PreH4 : (i < m_pre)) (PreH5 : (deg <> 0)) (PreH6 : (kinds = 3)) (PreH7 : (pivot = (-1))) (PreH8 : (3 <= n_pre)) (PreH9 : (n_pre <= 50)) (PreH10 : ((n_pre - 1 ) <= m_pre)) (PreH11 : (m_pre <= 1225)) (PreH12 : (m_pre = (Zlength (e)))) (PreH13 : ((Zlength (u_data)) = m_pre)) (PreH14 : ((Zlength (v_data)) = m_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH16 : (Pre n_pre e )) (PreH17 : (DegreePrefix n_pre e m_pre degrees )) (PreH18 : (PivotChoice n_pre degrees pivot )) (PreH19 : (0 <= i)) (PreH20 : (i <= m_pre)) (PreH21 : (first = 0)) (PreH22 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "kinds" ) )) # Int  |-> kinds)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_35 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (first = 0)) (PreH2 : ((Znth i u_data 0) = 0)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 3)) (PreH6 : (pivot = (-1))) (PreH7 : (3 <= n_pre)) (PreH8 : (n_pre <= 50)) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (m_pre <= 1225)) (PreH11 : (m_pre = (Zlength (e)))) (PreH12 : ((Zlength (u_data)) = m_pre)) (PreH13 : ((Zlength (v_data)) = m_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH15 : (Pre n_pre e )) (PreH16 : (DegreePrefix n_pre e m_pre degrees )) (PreH17 : (PivotChoice n_pre degrees pivot )) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : (first = 0)) (PreH21 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.seg colors_pre 0 (i + 1 ) (app (labels) ((cons (2) ((@nil Z))))) )
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "kinds" ) )) # Int  |-> kinds)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_36 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (first <> 0)) (PreH2 : ((Znth i u_data 0) = 0)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 3)) (PreH6 : (pivot = (-1))) (PreH7 : (3 <= n_pre)) (PreH8 : (n_pre <= 50)) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (m_pre <= 1225)) (PreH11 : (m_pre = (Zlength (e)))) (PreH12 : ((Zlength (u_data)) = m_pre)) (PreH13 : ((Zlength (v_data)) = m_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH15 : (Pre n_pre e )) (PreH16 : (DegreePrefix n_pre e m_pre degrees )) (PreH17 : (PivotChoice n_pre degrees pivot )) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : (first = 1)) (PreH21 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.seg colors_pre 0 (i + 1 ) (app (labels) ((cons (1) ((@nil Z))))) )
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "kinds" ) )) # Int  |-> kinds)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_37 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (first <> 0)) (PreH2 : ((Znth i v_data 0) = 0)) (PreH3 : ((Znth i u_data 0) <> 0)) (PreH4 : (i < m_pre)) (PreH5 : (deg <> 0)) (PreH6 : (kinds = 3)) (PreH7 : (pivot = (-1))) (PreH8 : (3 <= n_pre)) (PreH9 : (n_pre <= 50)) (PreH10 : ((n_pre - 1 ) <= m_pre)) (PreH11 : (m_pre <= 1225)) (PreH12 : (m_pre = (Zlength (e)))) (PreH13 : ((Zlength (u_data)) = m_pre)) (PreH14 : ((Zlength (v_data)) = m_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH16 : (Pre n_pre e )) (PreH17 : (DegreePrefix n_pre e m_pre degrees )) (PreH18 : (PivotChoice n_pre degrees pivot )) (PreH19 : (0 <= i)) (PreH20 : (i <= m_pre)) (PreH21 : (first = 1)) (PreH22 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.seg colors_pre 0 (i + 1 ) (app (labels) ((cons (1) ((@nil Z))))) )
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "kinds" ) )) # Int  |-> kinds)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  (IntArray.full deg n_pre degrees )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_38 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (first = 0)) (PreH2 : ((Znth i v_data 0) = 0)) (PreH3 : ((Znth i u_data 0) <> 0)) (PreH4 : (i < m_pre)) (PreH5 : (deg <> 0)) (PreH6 : (kinds = 3)) (PreH7 : (pivot = (-1))) (PreH8 : (3 <= n_pre)) (PreH9 : (n_pre <= 50)) (PreH10 : ((n_pre - 1 ) <= m_pre)) (PreH11 : (m_pre <= 1225)) (PreH12 : (m_pre = (Zlength (e)))) (PreH13 : ((Zlength (u_data)) = m_pre)) (PreH14 : ((Zlength (v_data)) = m_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH16 : (Pre n_pre e )) (PreH17 : (DegreePrefix n_pre e m_pre degrees )) (PreH18 : (PivotChoice n_pre degrees pivot )) (PreH19 : (0 <= i)) (PreH20 : (i <= m_pre)) (PreH21 : (first = 0)) (PreH22 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.seg colors_pre 0 (i + 1 ) (app (labels) ((cons (2) ((@nil Z))))) )
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "kinds" ) )) # Int  |-> kinds)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  (IntArray.full deg n_pre degrees )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_39 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i v_data 0) <> 0)) (PreH2 : ((Znth i u_data 0) <> 0)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 3)) (PreH6 : (pivot = (-1))) (PreH7 : (3 <= n_pre)) (PreH8 : (n_pre <= 50)) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (m_pre <= 1225)) (PreH11 : (m_pre = (Zlength (e)))) (PreH12 : ((Zlength (u_data)) = m_pre)) (PreH13 : ((Zlength (v_data)) = m_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH15 : (Pre n_pre e )) (PreH16 : (DegreePrefix n_pre e m_pre degrees )) (PreH17 : (PivotChoice n_pre degrees pivot )) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : (first = 1)) (PreH21 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "kinds" ) )) # Int  |-> kinds)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition solver_safety_wit_40 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i v_data 0) <> 0)) (PreH2 : ((Znth i u_data 0) <> 0)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 3)) (PreH6 : (pivot = (-1))) (PreH7 : (3 <= n_pre)) (PreH8 : (n_pre <= 50)) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (m_pre <= 1225)) (PreH11 : (m_pre = (Zlength (e)))) (PreH12 : ((Zlength (u_data)) = m_pre)) (PreH13 : ((Zlength (v_data)) = m_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH15 : (Pre n_pre e )) (PreH16 : (DegreePrefix n_pre e m_pre degrees )) (PreH17 : (PivotChoice n_pre degrees pivot )) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : (first = 0)) (PreH21 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "kinds" ) )) # Int  |-> kinds)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition solver_safety_wit_41 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (first = 0)) (PreH2 : ((Znth i u_data 0) = 0)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 3)) (PreH6 : (pivot = (-1))) (PreH7 : (3 <= n_pre)) (PreH8 : (n_pre <= 50)) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (m_pre <= 1225)) (PreH11 : (m_pre = (Zlength (e)))) (PreH12 : ((Zlength (u_data)) = m_pre)) (PreH13 : ((Zlength (v_data)) = m_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH15 : (Pre n_pre e )) (PreH16 : (DegreePrefix n_pre e m_pre degrees )) (PreH17 : (PivotChoice n_pre degrees pivot )) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : (first = 0)) (PreH21 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.seg colors_pre 0 (i + 1 ) (app (labels) ((cons (2) ((@nil Z))))) )
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "kinds" ) )) # Int  |-> kinds)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "first" ) )) # Int  |-> 0)
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full deg n_pre degrees )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_42 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (first <> 0)) (PreH2 : ((Znth i u_data 0) = 0)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 3)) (PreH6 : (pivot = (-1))) (PreH7 : (3 <= n_pre)) (PreH8 : (n_pre <= 50)) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (m_pre <= 1225)) (PreH11 : (m_pre = (Zlength (e)))) (PreH12 : ((Zlength (u_data)) = m_pre)) (PreH13 : ((Zlength (v_data)) = m_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH15 : (Pre n_pre e )) (PreH16 : (DegreePrefix n_pre e m_pre degrees )) (PreH17 : (PivotChoice n_pre degrees pivot )) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : (first = 1)) (PreH21 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.seg colors_pre 0 (i + 1 ) (app (labels) ((cons (1) ((@nil Z))))) )
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "kinds" ) )) # Int  |-> kinds)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "first" ) )) # Int  |-> 0)
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full deg n_pre degrees )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_43 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (first <> 0)) (PreH2 : ((Znth i v_data 0) = 0)) (PreH3 : ((Znth i u_data 0) <> 0)) (PreH4 : (i < m_pre)) (PreH5 : (deg <> 0)) (PreH6 : (kinds = 3)) (PreH7 : (pivot = (-1))) (PreH8 : (3 <= n_pre)) (PreH9 : (n_pre <= 50)) (PreH10 : ((n_pre - 1 ) <= m_pre)) (PreH11 : (m_pre <= 1225)) (PreH12 : (m_pre = (Zlength (e)))) (PreH13 : ((Zlength (u_data)) = m_pre)) (PreH14 : ((Zlength (v_data)) = m_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH16 : (Pre n_pre e )) (PreH17 : (DegreePrefix n_pre e m_pre degrees )) (PreH18 : (PivotChoice n_pre degrees pivot )) (PreH19 : (0 <= i)) (PreH20 : (i <= m_pre)) (PreH21 : (first = 1)) (PreH22 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.seg colors_pre 0 (i + 1 ) (app (labels) ((cons (1) ((@nil Z))))) )
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "kinds" ) )) # Int  |-> kinds)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "first" ) )) # Int  |-> 0)
  **  (IntArray.full deg n_pre degrees )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_44 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (first = 0)) (PreH2 : ((Znth i v_data 0) = 0)) (PreH3 : ((Znth i u_data 0) <> 0)) (PreH4 : (i < m_pre)) (PreH5 : (deg <> 0)) (PreH6 : (kinds = 3)) (PreH7 : (pivot = (-1))) (PreH8 : (3 <= n_pre)) (PreH9 : (n_pre <= 50)) (PreH10 : ((n_pre - 1 ) <= m_pre)) (PreH11 : (m_pre <= 1225)) (PreH12 : (m_pre = (Zlength (e)))) (PreH13 : ((Zlength (u_data)) = m_pre)) (PreH14 : ((Zlength (v_data)) = m_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH16 : (Pre n_pre e )) (PreH17 : (DegreePrefix n_pre e m_pre degrees )) (PreH18 : (PivotChoice n_pre degrees pivot )) (PreH19 : (0 <= i)) (PreH20 : (i <= m_pre)) (PreH21 : (first = 0)) (PreH22 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.seg colors_pre 0 (i + 1 ) (app (labels) ((cons (2) ((@nil Z))))) )
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "kinds" ) )) # Int  |-> kinds)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "first" ) )) # Int  |-> 0)
  **  (IntArray.full deg n_pre degrees )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_45 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i v_data 0) <> 0)) (PreH2 : ((Znth i u_data 0) <> 0)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 3)) (PreH6 : (pivot = (-1))) (PreH7 : (3 <= n_pre)) (PreH8 : (n_pre <= 50)) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (m_pre <= 1225)) (PreH11 : (m_pre = (Zlength (e)))) (PreH12 : ((Zlength (u_data)) = m_pre)) (PreH13 : ((Zlength (v_data)) = m_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH15 : (Pre n_pre e )) (PreH16 : (DegreePrefix n_pre e m_pre degrees )) (PreH17 : (PivotChoice n_pre degrees pivot )) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : (first = 1)) (PreH21 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.seg colors_pre 0 (i + 1 ) (app (labels) ((cons (3) ((@nil Z))))) )
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "kinds" ) )) # Int  |-> kinds)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  (IntArray.full deg n_pre degrees )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_46 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i v_data 0) <> 0)) (PreH2 : ((Znth i u_data 0) <> 0)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 3)) (PreH6 : (pivot = (-1))) (PreH7 : (3 <= n_pre)) (PreH8 : (n_pre <= 50)) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (m_pre <= 1225)) (PreH11 : (m_pre = (Zlength (e)))) (PreH12 : ((Zlength (u_data)) = m_pre)) (PreH13 : ((Zlength (v_data)) = m_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH15 : (Pre n_pre e )) (PreH16 : (DegreePrefix n_pre e m_pre degrees )) (PreH17 : (PivotChoice n_pre degrees pivot )) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : (first = 0)) (PreH21 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.seg colors_pre 0 (i + 1 ) (app (labels) ((cons (3) ((@nil Z))))) )
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  ((( &( "deg" ) )) # Ptr  |-> deg)
  **  ((( &( "kinds" ) )) # Int  |-> kinds)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  (IntArray.full deg n_pre degrees )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval <> 0)) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : ((n_pre - 1 ) <= (Zlength (e)))) (PreH5 : ((Zlength (e)) <= 1225)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (e)))) -> (((0 <= (fst ((Znth i e __default__Prod_Z_Z)))) /\ ((fst ((Znth i e __default__Prod_Z_Z))) < n_pre)) /\ ((0 <= (snd ((Znth i e __default__Prod_Z_Z)))) /\ ((snd ((Znth i e __default__Prod_Z_Z))) < n_pre))))) (PreH7 : (Pre n_pre e )) (PreH8 : (m_pre = (Zlength (e)))) (PreH9 : ((Zlength (u_data)) = m_pre)) (PreH10 : ((Zlength (v_data)) = m_pre)) (PreH11 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((Znth i_2 u_data 0) = (fst ((Znth i_2 e __default__Prod_Z_Z)))) /\ ((Znth i_2 v_data 0) = (snd ((Znth i_2 e __default__Prod_Z_Z))))))) ,
  (IntArray.full retval n_pre (repeat_Z (0) (n_pre)) )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
|--
  EX (degrees: (@list Z)) ,
  “ (retval <> 0) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (DegreePrefix n_pre e 0 degrees ) ” 
  &&  “ forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees 0)) /\ ((Znth x degrees 0) <= (2 * 0 )))) ”
  &&  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
  **  (IntArray.full retval n_pre degrees )
) \/
(
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval <> 0)) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : ((n_pre - 1 ) <= (Zlength (e)))) (PreH5 : ((Zlength (e)) <= 1225)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (e)))) -> (((0 <= (fst ((Znth i e __default__Prod_Z_Z)))) /\ ((fst ((Znth i e __default__Prod_Z_Z))) < n_pre)) /\ ((0 <= (snd ((Znth i e __default__Prod_Z_Z)))) /\ ((snd ((Znth i e __default__Prod_Z_Z))) < n_pre))))) (PreH7 : (Pre n_pre e )) (PreH8 : (m_pre = (Zlength (e)))) (PreH9 : ((Zlength (u_data)) = m_pre)) (PreH10 : ((Zlength (v_data)) = m_pre)) (PreH11 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((Znth i_2 u_data 0) = (fst ((Znth i_2 e __default__Prod_Z_Z)))) /\ ((Znth i_2 v_data 0) = (snd ((Znth i_2 e __default__Prod_Z_Z))))))) ,
  TT && emp 
|--
  “ forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x (repeat_Z (0) (n_pre)) 0)) /\ ((Znth x (repeat_Z (0) (n_pre)) 0) <= (2 * 0 )))) ” 
  &&  “ (DegreePrefix n_pre e 0 (repeat_Z (0) (n_pre)) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval <> 0)) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : ((n_pre - 1 ) <= (Zlength (e)))) (PreH5 : ((Zlength (e)) <= 1225)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (e)))) -> (((0 <= (fst ((Znth i e __default__Prod_Z_Z)))) /\ ((fst ((Znth i e __default__Prod_Z_Z))) < n_pre)) /\ ((0 <= (snd ((Znth i e __default__Prod_Z_Z)))) /\ ((snd ((Znth i e __default__Prod_Z_Z))) < n_pre))))) (PreH7 : (Pre n_pre e )) (PreH8 : (m_pre = (Zlength (e)))) (PreH9 : ((Zlength (u_data)) = m_pre)) (PreH10 : ((Zlength (v_data)) = m_pre)) (PreH11 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((Znth i_2 u_data 0) = (fst ((Znth i_2 e __default__Prod_Z_Z)))) /\ ((Znth i_2 v_data 0) = (snd ((Znth i_2 e __default__Prod_Z_Z))))))) ,
  forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x (repeat_Z (0) (n_pre)) 0)) /\ ((Znth x (repeat_Z (0) (n_pre)) 0) <= (2 * 0 ))))
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval <> 0)) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : ((n_pre - 1 ) <= (Zlength (e)))) (PreH5 : ((Zlength (e)) <= 1225)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (e)))) -> (((0 <= (fst ((Znth i e __default__Prod_Z_Z)))) /\ ((fst ((Znth i e __default__Prod_Z_Z))) < n_pre)) /\ ((0 <= (snd ((Znth i e __default__Prod_Z_Z)))) /\ ((snd ((Znth i e __default__Prod_Z_Z))) < n_pre))))) (PreH7 : (Pre n_pre e )) (PreH8 : (m_pre = (Zlength (e)))) (PreH9 : ((Zlength (u_data)) = m_pre)) (PreH10 : ((Zlength (v_data)) = m_pre)) (PreH11 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((Znth i_2 u_data 0) = (fst ((Znth i_2 e __default__Prod_Z_Z)))) /\ ((Znth i_2 v_data 0) = (snd ((Znth i_2 e __default__Prod_Z_Z))))))) ,
  (DegreePrefix n_pre e 0 (repeat_Z (0) (n_pre)) )
.

Definition solver_entail_wit_1_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval <> 0)) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : ((n_pre - 1 ) <= (Zlength (e)))) (PreH5 : ((Zlength (e)) <= 1225)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (e)))) -> (((0 <= (fst ((Znth i e __default__Prod_Z_Z)))) /\ ((fst ((Znth i e __default__Prod_Z_Z))) < n_pre)) /\ ((0 <= (snd ((Znth i e __default__Prod_Z_Z)))) /\ ((snd ((Znth i e __default__Prod_Z_Z))) < n_pre))))) (PreH7 : (Pre n_pre e )) (PreH8 : (m_pre = (Zlength (e)))) (PreH9 : ((Zlength (u_data)) = m_pre)) (PreH10 : ((Zlength (v_data)) = m_pre)) (PreH11 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((Znth i_2 u_data 0) = (fst ((Znth i_2 e __default__Prod_Z_Z)))) /\ ((Znth i_2 v_data 0) = (snd ((Znth i_2 e __default__Prod_Z_Z))))))) ,
  forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))
.

Definition solver_entail_wit_2 := 
(
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees_2: (@list Z)) (i: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (DegreePrefix n_pre e i degrees_2 )) (PreH15 : forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees_2 0)) /\ ((Znth x degrees_2 0) <= (2 * i ))))) ,
  (IntArray.full deg n_pre (replace_Znth ((Znth i v_data 0)) (((Znth (Znth i v_data 0) (replace_Znth ((Znth i u_data 0)) (((Znth (Znth i u_data 0) degrees_2 0) + 1 )) (degrees_2)) 0) + 1 )) ((replace_Znth ((Znth i u_data 0)) (((Znth (Znth i u_data 0) degrees_2 0) + 1 )) (degrees_2)))) )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.undef_full colors_pre m_pre )
|--
  EX (degrees: (@list Z)) ,
  “ (deg <> 0) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= m_pre) ” 
  &&  “ (DegreePrefix n_pre e (i + 1 ) degrees ) ” 
  &&  “ forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees 0)) /\ ((Znth x degrees 0) <= (2 * (i + 1 ) )))) ”
  &&  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
  **  (IntArray.full deg n_pre degrees )
) \/
(
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees_2: (@list Z)) (i: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (DegreePrefix n_pre e i degrees_2 )) (PreH15 : forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees_2 0)) /\ ((Znth x degrees_2 0) <= (2 * i ))))) ,
  TT && emp 
|--
  “ (DegreePrefix n_pre e (i + 1 ) (replace_Znth ((Znth i v_data 0)) (((Znth (Znth i v_data 0) (replace_Znth ((Znth i u_data 0)) (((Znth (Znth i u_data 0) degrees_2 0) + 1 )) (degrees_2)) 0) + 1 )) ((replace_Znth ((Znth i u_data 0)) (((Znth (Znth i u_data 0) degrees_2 0) + 1 )) (degrees_2)))) ) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees_2: (@list Z)) (i: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (DegreePrefix n_pre e i degrees_2 )) (PreH15 : forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees_2 0)) /\ ((Znth x degrees_2 0) <= (2 * i ))))) ,
  (DegreePrefix n_pre e (i + 1 ) (replace_Znth ((Znth i v_data 0)) (((Znth (Znth i v_data 0) (replace_Znth ((Znth i u_data 0)) (((Znth (Znth i u_data 0) degrees_2 0) + 1 )) (degrees_2)) 0) + 1 )) ((replace_Znth ((Znth i u_data 0)) (((Znth (Znth i u_data 0) degrees_2 0) + 1 )) (degrees_2)))) )
.

Definition solver_entail_wit_3 := 
(
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees_2: (@list Z)) (i: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i >= m_pre)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> (((((0 <= (Znth k_2 u_data 0)) /\ ((Znth k_2 u_data 0) < n_pre)) /\ ((0 <= (Znth k_2 v_data 0)) /\ ((Znth k_2 v_data 0) < n_pre))) /\ ((Znth k_2 u_data 0) = (fst ((Znth k_2 e __default__Prod_Z_Z))))) /\ ((Znth k_2 v_data 0) = (snd ((Znth k_2 e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (DegreePrefix n_pre e i degrees_2 )) (PreH15 : forall (x_2: Z) , (((0 <= x_2) /\ (x_2 < n_pre)) -> ((0 <= (Znth x_2 degrees_2 0)) /\ ((Znth x_2 degrees_2 0) <= (2 * i ))))) ,
  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
  **  (IntArray.full deg n_pre degrees_2 )
|--
  EX (degrees: (@list Z)) ,
  “ (deg <> 0) ” 
  &&  “ ((-1) = (-1)) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (DegreePrefix n_pre e m_pre degrees ) ” 
  &&  “ (PivotPrefix n_pre degrees 0 ) ” 
  &&  “ forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees 0)) /\ ((Znth x degrees 0) <= (n_pre - 1 )))) ”
  &&  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
  **  (IntArray.full deg n_pre degrees )
) \/
(
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees_2: (@list Z)) (i: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i >= m_pre)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> (((((0 <= (Znth k_2 u_data 0)) /\ ((Znth k_2 u_data 0) < n_pre)) /\ ((0 <= (Znth k_2 v_data 0)) /\ ((Znth k_2 v_data 0) < n_pre))) /\ ((Znth k_2 u_data 0) = (fst ((Znth k_2 e __default__Prod_Z_Z))))) /\ ((Znth k_2 v_data 0) = (snd ((Znth k_2 e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (DegreePrefix n_pre e i degrees_2 )) (PreH15 : forall (x_2: Z) , (((0 <= x_2) /\ (x_2 < n_pre)) -> ((0 <= (Znth x_2 degrees_2 0)) /\ ((Znth x_2 degrees_2 0) <= (2 * i ))))) ,
  TT && emp 
|--
  “ forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees_2 0)) /\ ((Znth x degrees_2 0) <= (n_pre - 1 )))) ” 
  &&  “ (PivotPrefix n_pre degrees_2 0 ) ” 
  &&  “ (DegreePrefix n_pre e m_pre degrees_2 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees_2: (@list Z)) (i: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i >= m_pre)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> (((((0 <= (Znth k_2 u_data 0)) /\ ((Znth k_2 u_data 0) < n_pre)) /\ ((0 <= (Znth k_2 v_data 0)) /\ ((Znth k_2 v_data 0) < n_pre))) /\ ((Znth k_2 u_data 0) = (fst ((Znth k_2 e __default__Prod_Z_Z))))) /\ ((Znth k_2 v_data 0) = (snd ((Znth k_2 e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (DegreePrefix n_pre e i degrees_2 )) (PreH15 : forall (x_2: Z) , (((0 <= x_2) /\ (x_2 < n_pre)) -> ((0 <= (Znth x_2 degrees_2 0)) /\ ((Znth x_2 degrees_2 0) <= (2 * i ))))) ,
  forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees_2 0)) /\ ((Znth x degrees_2 0) <= (n_pre - 1 ))))
.

Definition solver_entail_wit_3_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees_2: (@list Z)) (i: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i >= m_pre)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> (((((0 <= (Znth k_2 u_data 0)) /\ ((Znth k_2 u_data 0) < n_pre)) /\ ((0 <= (Znth k_2 v_data 0)) /\ ((Znth k_2 v_data 0) < n_pre))) /\ ((Znth k_2 u_data 0) = (fst ((Znth k_2 e __default__Prod_Z_Z))))) /\ ((Znth k_2 v_data 0) = (snd ((Znth k_2 e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (DegreePrefix n_pre e i degrees_2 )) (PreH15 : forall (x_2: Z) , (((0 <= x_2) /\ (x_2 < n_pre)) -> ((0 <= (Znth x_2 degrees_2 0)) /\ ((Znth x_2 degrees_2 0) <= (2 * i ))))) ,
  (PivotPrefix n_pre degrees_2 0 )
.

Definition solver_entail_wit_3_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees_2: (@list Z)) (i: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i >= m_pre)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> (((((0 <= (Znth k_2 u_data 0)) /\ ((Znth k_2 u_data 0) < n_pre)) /\ ((0 <= (Znth k_2 v_data 0)) /\ ((Znth k_2 v_data 0) < n_pre))) /\ ((Znth k_2 u_data 0) = (fst ((Znth k_2 e __default__Prod_Z_Z))))) /\ ((Znth k_2 v_data 0) = (snd ((Znth k_2 e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (DegreePrefix n_pre e i degrees_2 )) (PreH15 : forall (x_2: Z) , (((0 <= x_2) /\ (x_2 < n_pre)) -> ((0 <= (Znth x_2 degrees_2 0)) /\ ((Znth x_2 degrees_2 0) <= (2 * i ))))) ,
  (DegreePrefix n_pre e m_pre degrees_2 )
.

Definition solver_entail_wit_3_split_goal_4 := 
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees_2: (@list Z)) (i: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i >= m_pre)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> (((((0 <= (Znth k_2 u_data 0)) /\ ((Znth k_2 u_data 0) < n_pre)) /\ ((0 <= (Znth k_2 v_data 0)) /\ ((Znth k_2 v_data 0) < n_pre))) /\ ((Znth k_2 u_data 0) = (fst ((Znth k_2 e __default__Prod_Z_Z))))) /\ ((Znth k_2 v_data 0) = (snd ((Znth k_2 e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (DegreePrefix n_pre e i degrees_2 )) (PreH15 : forall (x_2: Z) , (((0 <= x_2) /\ (x_2 < n_pre)) -> ((0 <= (Znth x_2 degrees_2 0)) /\ ((Znth x_2 degrees_2 0) <= (2 * i ))))) ,
  forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))
.

Definition solver_entail_wit_4 := 
(
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees_2: (@list Z)) (i: Z) (pivot: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i degrees_2 0) >= (n_pre - 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (deg <> 0)) (PreH4 : (pivot = (-1))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : ((n_pre - 1 ) <= m_pre)) (PreH8 : (m_pre <= 1225)) (PreH9 : (m_pre = (Zlength (e)))) (PreH10 : ((Zlength (u_data)) = m_pre)) (PreH11 : ((Zlength (v_data)) = m_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH13 : (Pre n_pre e )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH17 : (PivotPrefix n_pre degrees_2 i )) (PreH18 : forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees_2 0)) /\ ((Znth x degrees_2 0) <= (n_pre - 1 ))))) ,
  (IntArray.full deg n_pre degrees_2 )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
|--
  EX (degrees: (@list Z)) ,
  “ (deg <> 0) ” 
  &&  “ (pivot = (-1)) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (DegreePrefix n_pre e m_pre degrees ) ” 
  &&  “ (PivotPrefix n_pre degrees (i + 1 ) ) ” 
  &&  “ forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees 0)) /\ ((Znth x degrees 0) <= (n_pre - 1 )))) ”
  &&  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
  **  (IntArray.full deg n_pre degrees )
) \/
(
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees_2: (@list Z)) (i: Z) (pivot: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i degrees_2 0) >= (n_pre - 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (deg <> 0)) (PreH4 : (pivot = (-1))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : ((n_pre - 1 ) <= m_pre)) (PreH8 : (m_pre <= 1225)) (PreH9 : (m_pre = (Zlength (e)))) (PreH10 : ((Zlength (u_data)) = m_pre)) (PreH11 : ((Zlength (v_data)) = m_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH13 : (Pre n_pre e )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH17 : (PivotPrefix n_pre degrees_2 i )) (PreH18 : forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees_2 0)) /\ ((Znth x degrees_2 0) <= (n_pre - 1 ))))) ,
  TT && emp 
|--
  “ (PivotPrefix n_pre degrees_2 (i + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees_2: (@list Z)) (i: Z) (pivot: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i degrees_2 0) >= (n_pre - 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (deg <> 0)) (PreH4 : (pivot = (-1))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : ((n_pre - 1 ) <= m_pre)) (PreH8 : (m_pre <= 1225)) (PreH9 : (m_pre = (Zlength (e)))) (PreH10 : ((Zlength (u_data)) = m_pre)) (PreH11 : ((Zlength (v_data)) = m_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH13 : (Pre n_pre e )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH17 : (PivotPrefix n_pre degrees_2 i )) (PreH18 : forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees_2 0)) /\ ((Znth x degrees_2 0) <= (n_pre - 1 ))))) ,
  (PivotPrefix n_pre degrees_2 (i + 1 ) )
.

Definition solver_entail_wit_5_1 := 
(
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees_2: (@list Z)) (i: Z) (pivot: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i >= n_pre)) (PreH2 : (deg <> 0)) (PreH3 : (pivot = (-1))) (PreH4 : (3 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : ((n_pre - 1 ) <= m_pre)) (PreH7 : (m_pre <= 1225)) (PreH8 : (m_pre = (Zlength (e)))) (PreH9 : ((Zlength (u_data)) = m_pre)) (PreH10 : ((Zlength (v_data)) = m_pre)) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> (((((0 <= (Znth k_2 u_data 0)) /\ ((Znth k_2 u_data 0) < n_pre)) /\ ((0 <= (Znth k_2 v_data 0)) /\ ((Znth k_2 v_data 0) < n_pre))) /\ ((Znth k_2 u_data 0) = (fst ((Znth k_2 e __default__Prod_Z_Z))))) /\ ((Znth k_2 v_data 0) = (snd ((Znth k_2 e __default__Prod_Z_Z))))))) (PreH12 : (Pre n_pre e )) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH16 : (PivotPrefix n_pre degrees_2 i )) (PreH17 : forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees_2 0)) /\ ((Znth x degrees_2 0) <= (n_pre - 1 ))))) ,
  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
  **  (IntArray.full deg n_pre degrees_2 )
|--
  EX (degrees: (@list Z)) ,
  “ (deg <> 0) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (DegreePrefix n_pre e m_pre degrees ) ” 
  &&  “ (PivotChoice n_pre degrees pivot ) ”
  &&  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
  **  (IntArray.full deg n_pre degrees )
) \/
(
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees_2: (@list Z)) (i: Z) (pivot: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i >= n_pre)) (PreH2 : (deg <> 0)) (PreH3 : (pivot = (-1))) (PreH4 : (3 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : ((n_pre - 1 ) <= m_pre)) (PreH7 : (m_pre <= 1225)) (PreH8 : (m_pre = (Zlength (e)))) (PreH9 : ((Zlength (u_data)) = m_pre)) (PreH10 : ((Zlength (v_data)) = m_pre)) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> (((((0 <= (Znth k_2 u_data 0)) /\ ((Znth k_2 u_data 0) < n_pre)) /\ ((0 <= (Znth k_2 v_data 0)) /\ ((Znth k_2 v_data 0) < n_pre))) /\ ((Znth k_2 u_data 0) = (fst ((Znth k_2 e __default__Prod_Z_Z))))) /\ ((Znth k_2 v_data 0) = (snd ((Znth k_2 e __default__Prod_Z_Z))))))) (PreH12 : (Pre n_pre e )) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH16 : (PivotPrefix n_pre degrees_2 i )) (PreH17 : forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees_2 0)) /\ ((Znth x degrees_2 0) <= (n_pre - 1 ))))) ,
  TT && emp 
|--
  “ (PivotChoice n_pre degrees_2 (-1) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ”
  &&  emp
).

Definition solver_entail_wit_5_1_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees_2: (@list Z)) (i: Z) (pivot: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i >= n_pre)) (PreH2 : (deg <> 0)) (PreH3 : (pivot = (-1))) (PreH4 : (3 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : ((n_pre - 1 ) <= m_pre)) (PreH7 : (m_pre <= 1225)) (PreH8 : (m_pre = (Zlength (e)))) (PreH9 : ((Zlength (u_data)) = m_pre)) (PreH10 : ((Zlength (v_data)) = m_pre)) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> (((((0 <= (Znth k_2 u_data 0)) /\ ((Znth k_2 u_data 0) < n_pre)) /\ ((0 <= (Znth k_2 v_data 0)) /\ ((Znth k_2 v_data 0) < n_pre))) /\ ((Znth k_2 u_data 0) = (fst ((Znth k_2 e __default__Prod_Z_Z))))) /\ ((Znth k_2 v_data 0) = (snd ((Znth k_2 e __default__Prod_Z_Z))))))) (PreH12 : (Pre n_pre e )) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH16 : (PivotPrefix n_pre degrees_2 i )) (PreH17 : forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees_2 0)) /\ ((Znth x degrees_2 0) <= (n_pre - 1 ))))) ,
  (PivotChoice n_pre degrees_2 (-1) )
.

Definition solver_entail_wit_5_1_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees_2: (@list Z)) (i: Z) (pivot: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i >= n_pre)) (PreH2 : (deg <> 0)) (PreH3 : (pivot = (-1))) (PreH4 : (3 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : ((n_pre - 1 ) <= m_pre)) (PreH7 : (m_pre <= 1225)) (PreH8 : (m_pre = (Zlength (e)))) (PreH9 : ((Zlength (u_data)) = m_pre)) (PreH10 : ((Zlength (v_data)) = m_pre)) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> (((((0 <= (Znth k_2 u_data 0)) /\ ((Znth k_2 u_data 0) < n_pre)) /\ ((0 <= (Znth k_2 v_data 0)) /\ ((Znth k_2 v_data 0) < n_pre))) /\ ((Znth k_2 u_data 0) = (fst ((Znth k_2 e __default__Prod_Z_Z))))) /\ ((Znth k_2 v_data 0) = (snd ((Znth k_2 e __default__Prod_Z_Z))))))) (PreH12 : (Pre n_pre e )) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH16 : (PivotPrefix n_pre degrees_2 i )) (PreH17 : forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees_2 0)) /\ ((Znth x degrees_2 0) <= (n_pre - 1 ))))) ,
  forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))
.

Definition solver_entail_wit_5_2 := 
(
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees_2: (@list Z)) (i: Z) (pivot: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i degrees_2 0) < (n_pre - 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (deg <> 0)) (PreH4 : (pivot = (-1))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : ((n_pre - 1 ) <= m_pre)) (PreH8 : (m_pre <= 1225)) (PreH9 : (m_pre = (Zlength (e)))) (PreH10 : ((Zlength (u_data)) = m_pre)) (PreH11 : ((Zlength (v_data)) = m_pre)) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> (((((0 <= (Znth k_2 u_data 0)) /\ ((Znth k_2 u_data 0) < n_pre)) /\ ((0 <= (Znth k_2 v_data 0)) /\ ((Znth k_2 v_data 0) < n_pre))) /\ ((Znth k_2 u_data 0) = (fst ((Znth k_2 e __default__Prod_Z_Z))))) /\ ((Znth k_2 v_data 0) = (snd ((Znth k_2 e __default__Prod_Z_Z))))))) (PreH13 : (Pre n_pre e )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH17 : (PivotPrefix n_pre degrees_2 i )) (PreH18 : forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees_2 0)) /\ ((Znth x degrees_2 0) <= (n_pre - 1 ))))) ,
  (IntArray.full deg n_pre degrees_2 )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
|--
  EX (degrees: (@list Z)) ,
  “ (deg <> 0) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (DegreePrefix n_pre e m_pre degrees ) ” 
  &&  “ (PivotChoice n_pre degrees i ) ”
  &&  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
  **  (IntArray.full deg n_pre degrees )
) \/
(
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees_2: (@list Z)) (i: Z) (pivot: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i degrees_2 0) < (n_pre - 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (deg <> 0)) (PreH4 : (pivot = (-1))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : ((n_pre - 1 ) <= m_pre)) (PreH8 : (m_pre <= 1225)) (PreH9 : (m_pre = (Zlength (e)))) (PreH10 : ((Zlength (u_data)) = m_pre)) (PreH11 : ((Zlength (v_data)) = m_pre)) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> (((((0 <= (Znth k_2 u_data 0)) /\ ((Znth k_2 u_data 0) < n_pre)) /\ ((0 <= (Znth k_2 v_data 0)) /\ ((Znth k_2 v_data 0) < n_pre))) /\ ((Znth k_2 u_data 0) = (fst ((Znth k_2 e __default__Prod_Z_Z))))) /\ ((Znth k_2 v_data 0) = (snd ((Znth k_2 e __default__Prod_Z_Z))))))) (PreH13 : (Pre n_pre e )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH17 : (PivotPrefix n_pre degrees_2 i )) (PreH18 : forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees_2 0)) /\ ((Znth x degrees_2 0) <= (n_pre - 1 ))))) ,
  TT && emp 
|--
  “ (PivotChoice n_pre degrees_2 i ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ”
  &&  emp
).

Definition solver_entail_wit_5_2_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees_2: (@list Z)) (i: Z) (pivot: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i degrees_2 0) < (n_pre - 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (deg <> 0)) (PreH4 : (pivot = (-1))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : ((n_pre - 1 ) <= m_pre)) (PreH8 : (m_pre <= 1225)) (PreH9 : (m_pre = (Zlength (e)))) (PreH10 : ((Zlength (u_data)) = m_pre)) (PreH11 : ((Zlength (v_data)) = m_pre)) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> (((((0 <= (Znth k_2 u_data 0)) /\ ((Znth k_2 u_data 0) < n_pre)) /\ ((0 <= (Znth k_2 v_data 0)) /\ ((Znth k_2 v_data 0) < n_pre))) /\ ((Znth k_2 u_data 0) = (fst ((Znth k_2 e __default__Prod_Z_Z))))) /\ ((Znth k_2 v_data 0) = (snd ((Znth k_2 e __default__Prod_Z_Z))))))) (PreH13 : (Pre n_pre e )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH17 : (PivotPrefix n_pre degrees_2 i )) (PreH18 : forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees_2 0)) /\ ((Znth x degrees_2 0) <= (n_pre - 1 ))))) ,
  (PivotChoice n_pre degrees_2 i )
.

Definition solver_entail_wit_5_2_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees_2: (@list Z)) (i: Z) (pivot: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i degrees_2 0) < (n_pre - 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (deg <> 0)) (PreH4 : (pivot = (-1))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : ((n_pre - 1 ) <= m_pre)) (PreH8 : (m_pre <= 1225)) (PreH9 : (m_pre = (Zlength (e)))) (PreH10 : ((Zlength (u_data)) = m_pre)) (PreH11 : ((Zlength (v_data)) = m_pre)) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> (((((0 <= (Znth k_2 u_data 0)) /\ ((Znth k_2 u_data 0) < n_pre)) /\ ((0 <= (Znth k_2 v_data 0)) /\ ((Znth k_2 v_data 0) < n_pre))) /\ ((Znth k_2 u_data 0) = (fst ((Znth k_2 e __default__Prod_Z_Z))))) /\ ((Znth k_2 v_data 0) = (snd ((Znth k_2 e __default__Prod_Z_Z))))))) (PreH13 : (Pre n_pre e )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH17 : (PivotPrefix n_pre degrees_2 i )) (PreH18 : forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees_2 0)) /\ ((Znth x degrees_2 0) <= (n_pre - 1 ))))) ,
  forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))
.

Definition solver_entail_wit_6 := 
(
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees_2: (@list Z)) (deg: Z) (pivot: Z)  __default__Prod_Z_Z (PreH1 : (pivot >= 0)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> (((((0 <= (Znth k_2 u_data 0)) /\ ((Znth k_2 u_data 0) < n_pre)) /\ ((0 <= (Znth k_2 v_data 0)) /\ ((Znth k_2 v_data 0) < n_pre))) /\ ((Znth k_2 u_data 0) = (fst ((Znth k_2 e __default__Prod_Z_Z))))) /\ ((Znth k_2 v_data 0) = (snd ((Znth k_2 e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH13 : (PivotChoice n_pre degrees_2 pivot )) ,
  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
  **  (IntArray.full deg n_pre degrees_2 )
|--
  EX (labels: (@list Z))  (degrees: (@list Z)) ,
  “ (deg <> 0) ” 
  &&  “ (2 = 2) ” 
  &&  “ (0 <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (DegreePrefix n_pre e m_pre degrees ) ” 
  &&  “ (PivotChoice n_pre degrees pivot ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (PivotColorPrefix e pivot 0 labels ) ”
  &&  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 0 labels )
  **  (IntArray.undef_seg colors_pre 0 m_pre )
  **  (IntArray.full deg n_pre degrees )
) \/
(
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees_2: (@list Z)) (deg: Z) (pivot: Z)  __default__Prod_Z_Z (PreH1 : (pivot >= 0)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> (((((0 <= (Znth k_2 u_data 0)) /\ ((Znth k_2 u_data 0) < n_pre)) /\ ((0 <= (Znth k_2 v_data 0)) /\ ((Znth k_2 v_data 0) < n_pre))) /\ ((Znth k_2 u_data 0) = (fst ((Znth k_2 e __default__Prod_Z_Z))))) /\ ((Znth k_2 v_data 0) = (snd ((Znth k_2 e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH13 : (PivotChoice n_pre degrees_2 pivot )) ,
  TT && emp 
|--
  “ (PivotColorPrefix e pivot 0 (@nil Z) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (pivot < n_pre) ”
  &&  emp
).

Definition solver_entail_wit_6_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees_2: (@list Z)) (deg: Z) (pivot: Z)  __default__Prod_Z_Z (PreH1 : (pivot >= 0)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> (((((0 <= (Znth k_2 u_data 0)) /\ ((Znth k_2 u_data 0) < n_pre)) /\ ((0 <= (Znth k_2 v_data 0)) /\ ((Znth k_2 v_data 0) < n_pre))) /\ ((Znth k_2 u_data 0) = (fst ((Znth k_2 e __default__Prod_Z_Z))))) /\ ((Znth k_2 v_data 0) = (snd ((Znth k_2 e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH13 : (PivotChoice n_pre degrees_2 pivot )) ,
  (PivotColorPrefix e pivot 0 (@nil Z) )
.

Definition solver_entail_wit_6_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees_2: (@list Z)) (deg: Z) (pivot: Z)  __default__Prod_Z_Z (PreH1 : (pivot >= 0)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> (((((0 <= (Znth k_2 u_data 0)) /\ ((Znth k_2 u_data 0) < n_pre)) /\ ((0 <= (Znth k_2 v_data 0)) /\ ((Znth k_2 v_data 0) < n_pre))) /\ ((Znth k_2 u_data 0) = (fst ((Znth k_2 e __default__Prod_Z_Z))))) /\ ((Znth k_2 v_data 0) = (snd ((Znth k_2 e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH13 : (PivotChoice n_pre degrees_2 pivot )) ,
  forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))
.

Definition solver_entail_wit_6_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees_2: (@list Z)) (deg: Z) (pivot: Z)  __default__Prod_Z_Z (PreH1 : (pivot >= 0)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> (((((0 <= (Znth k_2 u_data 0)) /\ ((Znth k_2 u_data 0) < n_pre)) /\ ((0 <= (Znth k_2 v_data 0)) /\ ((Znth k_2 v_data 0) < n_pre))) /\ ((Znth k_2 u_data 0) = (fst ((Znth k_2 e __default__Prod_Z_Z))))) /\ ((Znth k_2 v_data 0) = (snd ((Znth k_2 e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH13 : (PivotChoice n_pre degrees_2 pivot )) ,
  (pivot < n_pre)
.

Definition solver_entail_wit_7_1 := 
(
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels_2: (@list Z)) (i: Z) (degrees_2: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i v_data 0) = pivot)) (PreH2 : ((Znth i u_data 0) <> pivot)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 2)) (PreH6 : (0 <= pivot)) (PreH7 : (pivot < n_pre)) (PreH8 : (3 <= n_pre)) (PreH9 : (n_pre <= 50)) (PreH10 : ((n_pre - 1 ) <= m_pre)) (PreH11 : (m_pre <= 1225)) (PreH12 : (m_pre = (Zlength (e)))) (PreH13 : ((Zlength (u_data)) = m_pre)) (PreH14 : ((Zlength (v_data)) = m_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH16 : (Pre n_pre e )) (PreH17 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH18 : (PivotChoice n_pre degrees_2 pivot )) (PreH19 : (0 <= i)) (PreH20 : (i <= m_pre)) (PreH21 : (PivotColorPrefix e pivot i labels_2 )) ,
  (IntArray.seg colors_pre 0 (i + 1 ) (app (labels_2) ((cons (1) ((@nil Z))))) )
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full deg n_pre degrees_2 )
|--
  EX (labels: (@list Z))  (degrees: (@list Z)) ,
  “ (deg <> 0) ” 
  &&  “ (kinds = 2) ” 
  &&  “ (0 <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (DegreePrefix n_pre e m_pre degrees ) ” 
  &&  “ (PivotChoice n_pre degrees pivot ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= m_pre) ” 
  &&  “ (PivotColorPrefix e pivot (i + 1 ) labels ) ”
  &&  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 (i + 1 ) labels )
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full deg n_pre degrees )
) \/
(
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels_2: (@list Z)) (i: Z) (degrees_2: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i v_data 0) = pivot)) (PreH2 : ((Znth i u_data 0) <> pivot)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 2)) (PreH6 : (0 <= pivot)) (PreH7 : (pivot < n_pre)) (PreH8 : (3 <= n_pre)) (PreH9 : (n_pre <= 50)) (PreH10 : ((n_pre - 1 ) <= m_pre)) (PreH11 : (m_pre <= 1225)) (PreH12 : (m_pre = (Zlength (e)))) (PreH13 : ((Zlength (u_data)) = m_pre)) (PreH14 : ((Zlength (v_data)) = m_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH16 : (Pre n_pre e )) (PreH17 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH18 : (PivotChoice n_pre degrees_2 pivot )) (PreH19 : (0 <= i)) (PreH20 : (i <= m_pre)) (PreH21 : (PivotColorPrefix e pivot i labels_2 )) ,
  TT && emp 
|--
  “ (PivotColorPrefix e pivot (i + 1 ) (app (labels_2) ((cons (1) ((@nil Z))))) ) ”
  &&  emp
).

Definition solver_entail_wit_7_1_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels_2: (@list Z)) (i: Z) (degrees_2: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i v_data 0) = pivot)) (PreH2 : ((Znth i u_data 0) <> pivot)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 2)) (PreH6 : (0 <= pivot)) (PreH7 : (pivot < n_pre)) (PreH8 : (3 <= n_pre)) (PreH9 : (n_pre <= 50)) (PreH10 : ((n_pre - 1 ) <= m_pre)) (PreH11 : (m_pre <= 1225)) (PreH12 : (m_pre = (Zlength (e)))) (PreH13 : ((Zlength (u_data)) = m_pre)) (PreH14 : ((Zlength (v_data)) = m_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH16 : (Pre n_pre e )) (PreH17 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH18 : (PivotChoice n_pre degrees_2 pivot )) (PreH19 : (0 <= i)) (PreH20 : (i <= m_pre)) (PreH21 : (PivotColorPrefix e pivot i labels_2 )) ,
  (PivotColorPrefix e pivot (i + 1 ) (app (labels_2) ((cons (1) ((@nil Z))))) )
.

Definition solver_entail_wit_7_2 := 
(
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels_2: (@list Z)) (i: Z) (degrees_2: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i u_data 0) = pivot)) (PreH2 : (i < m_pre)) (PreH3 : (deg <> 0)) (PreH4 : (kinds = 2)) (PreH5 : (0 <= pivot)) (PreH6 : (pivot < n_pre)) (PreH7 : (3 <= n_pre)) (PreH8 : (n_pre <= 50)) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (m_pre <= 1225)) (PreH11 : (m_pre = (Zlength (e)))) (PreH12 : ((Zlength (u_data)) = m_pre)) (PreH13 : ((Zlength (v_data)) = m_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH15 : (Pre n_pre e )) (PreH16 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH17 : (PivotChoice n_pre degrees_2 pivot )) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : (PivotColorPrefix e pivot i labels_2 )) ,
  (IntArray.seg colors_pre 0 (i + 1 ) (app (labels_2) ((cons (1) ((@nil Z))))) )
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full deg n_pre degrees_2 )
|--
  EX (labels: (@list Z))  (degrees: (@list Z)) ,
  “ (deg <> 0) ” 
  &&  “ (kinds = 2) ” 
  &&  “ (0 <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (DegreePrefix n_pre e m_pre degrees ) ” 
  &&  “ (PivotChoice n_pre degrees pivot ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= m_pre) ” 
  &&  “ (PivotColorPrefix e pivot (i + 1 ) labels ) ”
  &&  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 (i + 1 ) labels )
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full deg n_pre degrees )
) \/
(
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels_2: (@list Z)) (i: Z) (degrees_2: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i u_data 0) = pivot)) (PreH2 : (i < m_pre)) (PreH3 : (deg <> 0)) (PreH4 : (kinds = 2)) (PreH5 : (0 <= pivot)) (PreH6 : (pivot < n_pre)) (PreH7 : (3 <= n_pre)) (PreH8 : (n_pre <= 50)) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (m_pre <= 1225)) (PreH11 : (m_pre = (Zlength (e)))) (PreH12 : ((Zlength (u_data)) = m_pre)) (PreH13 : ((Zlength (v_data)) = m_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH15 : (Pre n_pre e )) (PreH16 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH17 : (PivotChoice n_pre degrees_2 pivot )) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : (PivotColorPrefix e pivot i labels_2 )) ,
  TT && emp 
|--
  “ (PivotColorPrefix e pivot (i + 1 ) (app (labels_2) ((cons (1) ((@nil Z))))) ) ”
  &&  emp
).

Definition solver_entail_wit_7_2_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels_2: (@list Z)) (i: Z) (degrees_2: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i u_data 0) = pivot)) (PreH2 : (i < m_pre)) (PreH3 : (deg <> 0)) (PreH4 : (kinds = 2)) (PreH5 : (0 <= pivot)) (PreH6 : (pivot < n_pre)) (PreH7 : (3 <= n_pre)) (PreH8 : (n_pre <= 50)) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (m_pre <= 1225)) (PreH11 : (m_pre = (Zlength (e)))) (PreH12 : ((Zlength (u_data)) = m_pre)) (PreH13 : ((Zlength (v_data)) = m_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH15 : (Pre n_pre e )) (PreH16 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH17 : (PivotChoice n_pre degrees_2 pivot )) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : (PivotColorPrefix e pivot i labels_2 )) ,
  (PivotColorPrefix e pivot (i + 1 ) (app (labels_2) ((cons (1) ((@nil Z))))) )
.

Definition solver_entail_wit_7_3 := 
(
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels_2: (@list Z)) (i: Z) (degrees_2: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i v_data 0) <> pivot)) (PreH2 : ((Znth i u_data 0) <> pivot)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 2)) (PreH6 : (0 <= pivot)) (PreH7 : (pivot < n_pre)) (PreH8 : (3 <= n_pre)) (PreH9 : (n_pre <= 50)) (PreH10 : ((n_pre - 1 ) <= m_pre)) (PreH11 : (m_pre <= 1225)) (PreH12 : (m_pre = (Zlength (e)))) (PreH13 : ((Zlength (u_data)) = m_pre)) (PreH14 : ((Zlength (v_data)) = m_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH16 : (Pre n_pre e )) (PreH17 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH18 : (PivotChoice n_pre degrees_2 pivot )) (PreH19 : (0 <= i)) (PreH20 : (i <= m_pre)) (PreH21 : (PivotColorPrefix e pivot i labels_2 )) ,
  (IntArray.seg colors_pre 0 (i + 1 ) (app (labels_2) ((cons (2) ((@nil Z))))) )
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full deg n_pre degrees_2 )
|--
  EX (labels: (@list Z))  (degrees: (@list Z)) ,
  “ (deg <> 0) ” 
  &&  “ (kinds = 2) ” 
  &&  “ (0 <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (DegreePrefix n_pre e m_pre degrees ) ” 
  &&  “ (PivotChoice n_pre degrees pivot ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= m_pre) ” 
  &&  “ (PivotColorPrefix e pivot (i + 1 ) labels ) ”
  &&  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 (i + 1 ) labels )
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full deg n_pre degrees )
) \/
(
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels_2: (@list Z)) (i: Z) (degrees_2: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i v_data 0) <> pivot)) (PreH2 : ((Znth i u_data 0) <> pivot)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 2)) (PreH6 : (0 <= pivot)) (PreH7 : (pivot < n_pre)) (PreH8 : (3 <= n_pre)) (PreH9 : (n_pre <= 50)) (PreH10 : ((n_pre - 1 ) <= m_pre)) (PreH11 : (m_pre <= 1225)) (PreH12 : (m_pre = (Zlength (e)))) (PreH13 : ((Zlength (u_data)) = m_pre)) (PreH14 : ((Zlength (v_data)) = m_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH16 : (Pre n_pre e )) (PreH17 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH18 : (PivotChoice n_pre degrees_2 pivot )) (PreH19 : (0 <= i)) (PreH20 : (i <= m_pre)) (PreH21 : (PivotColorPrefix e pivot i labels_2 )) ,
  TT && emp 
|--
  “ (PivotColorPrefix e pivot (i + 1 ) (app (labels_2) ((cons (2) ((@nil Z))))) ) ”
  &&  emp
).

Definition solver_entail_wit_7_3_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels_2: (@list Z)) (i: Z) (degrees_2: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i v_data 0) <> pivot)) (PreH2 : ((Znth i u_data 0) <> pivot)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 2)) (PreH6 : (0 <= pivot)) (PreH7 : (pivot < n_pre)) (PreH8 : (3 <= n_pre)) (PreH9 : (n_pre <= 50)) (PreH10 : ((n_pre - 1 ) <= m_pre)) (PreH11 : (m_pre <= 1225)) (PreH12 : (m_pre = (Zlength (e)))) (PreH13 : ((Zlength (u_data)) = m_pre)) (PreH14 : ((Zlength (v_data)) = m_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH16 : (Pre n_pre e )) (PreH17 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH18 : (PivotChoice n_pre degrees_2 pivot )) (PreH19 : (0 <= i)) (PreH20 : (i <= m_pre)) (PreH21 : (PivotColorPrefix e pivot i labels_2 )) ,
  (PivotColorPrefix e pivot (i + 1 ) (app (labels_2) ((cons (2) ((@nil Z))))) )
.

Definition solver_entail_wit_8 := 
(
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees_2: (@list Z)) (deg: Z) (pivot: Z)  __default__Prod_Z_Z (PreH1 : (pivot < 0)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> (((((0 <= (Znth k_2 u_data 0)) /\ ((Znth k_2 u_data 0) < n_pre)) /\ ((0 <= (Znth k_2 v_data 0)) /\ ((Znth k_2 v_data 0) < n_pre))) /\ ((Znth k_2 u_data 0) = (fst ((Znth k_2 e __default__Prod_Z_Z))))) /\ ((Znth k_2 v_data 0) = (snd ((Znth k_2 e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH13 : (PivotChoice n_pre degrees_2 pivot )) ,
  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
  **  (IntArray.full deg n_pre degrees_2 )
|--
  EX (labels: (@list Z))  (degrees: (@list Z)) ,
  “ (deg <> 0) ” 
  &&  “ (3 = 3) ” 
  &&  “ (pivot = (-1)) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (DegreePrefix n_pre e m_pre degrees ) ” 
  &&  “ (PivotChoice n_pre degrees pivot ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (1 = 1) ” 
  &&  “ (CompleteColorPrefix e 0 1 labels ) ”
  &&  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 0 labels )
  **  (IntArray.undef_seg colors_pre 0 m_pre )
  **  (IntArray.full deg n_pre degrees )
) \/
(
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees_2: (@list Z)) (deg: Z) (pivot: Z)  __default__Prod_Z_Z (PreH1 : (pivot < 0)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> (((((0 <= (Znth k_2 u_data 0)) /\ ((Znth k_2 u_data 0) < n_pre)) /\ ((0 <= (Znth k_2 v_data 0)) /\ ((Znth k_2 v_data 0) < n_pre))) /\ ((Znth k_2 u_data 0) = (fst ((Znth k_2 e __default__Prod_Z_Z))))) /\ ((Znth k_2 v_data 0) = (snd ((Znth k_2 e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH13 : (PivotChoice n_pre degrees_2 pivot )) ,
  TT && emp 
|--
  “ (CompleteColorPrefix e 0 1 (@nil Z) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (pivot = (-1)) ”
  &&  emp
).

Definition solver_entail_wit_8_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees_2: (@list Z)) (deg: Z) (pivot: Z)  __default__Prod_Z_Z (PreH1 : (pivot < 0)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> (((((0 <= (Znth k_2 u_data 0)) /\ ((Znth k_2 u_data 0) < n_pre)) /\ ((0 <= (Znth k_2 v_data 0)) /\ ((Znth k_2 v_data 0) < n_pre))) /\ ((Znth k_2 u_data 0) = (fst ((Znth k_2 e __default__Prod_Z_Z))))) /\ ((Znth k_2 v_data 0) = (snd ((Znth k_2 e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH13 : (PivotChoice n_pre degrees_2 pivot )) ,
  (CompleteColorPrefix e 0 1 (@nil Z) )
.

Definition solver_entail_wit_8_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees_2: (@list Z)) (deg: Z) (pivot: Z)  __default__Prod_Z_Z (PreH1 : (pivot < 0)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> (((((0 <= (Znth k_2 u_data 0)) /\ ((Znth k_2 u_data 0) < n_pre)) /\ ((0 <= (Znth k_2 v_data 0)) /\ ((Znth k_2 v_data 0) < n_pre))) /\ ((Znth k_2 u_data 0) = (fst ((Znth k_2 e __default__Prod_Z_Z))))) /\ ((Znth k_2 v_data 0) = (snd ((Znth k_2 e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH13 : (PivotChoice n_pre degrees_2 pivot )) ,
  forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))
.

Definition solver_entail_wit_8_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees_2: (@list Z)) (deg: Z) (pivot: Z)  __default__Prod_Z_Z (PreH1 : (pivot < 0)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> (((((0 <= (Znth k_2 u_data 0)) /\ ((Znth k_2 u_data 0) < n_pre)) /\ ((0 <= (Znth k_2 v_data 0)) /\ ((Znth k_2 v_data 0) < n_pre))) /\ ((Znth k_2 u_data 0) = (fst ((Znth k_2 e __default__Prod_Z_Z))))) /\ ((Znth k_2 v_data 0) = (snd ((Znth k_2 e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH13 : (PivotChoice n_pre degrees_2 pivot )) ,
  (pivot = (-1))
.

Definition solver_entail_wit_9_1 := 
(
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels_2: (@list Z)) (first: Z) (i: Z) (degrees_2: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (first = 0)) (PreH2 : ((Znth i u_data 0) = 0)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 3)) (PreH6 : (pivot = (-1))) (PreH7 : (3 <= n_pre)) (PreH8 : (n_pre <= 50)) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (m_pre <= 1225)) (PreH11 : (m_pre = (Zlength (e)))) (PreH12 : ((Zlength (u_data)) = m_pre)) (PreH13 : ((Zlength (v_data)) = m_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH15 : (Pre n_pre e )) (PreH16 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH17 : (PivotChoice n_pre degrees_2 pivot )) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : (first = 0)) (PreH21 : (CompleteColorPrefix e i first labels_2 )) ,
  (IntArray.seg colors_pre 0 (i + 1 ) (app (labels_2) ((cons (2) ((@nil Z))))) )
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full deg n_pre degrees_2 )
|--
  EX (labels: (@list Z))  (degrees: (@list Z)) ,
  “ (deg <> 0) ” 
  &&  “ (kinds = 3) ” 
  &&  “ (pivot = (-1)) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (DegreePrefix n_pre e m_pre degrees ) ” 
  &&  “ (PivotChoice n_pre degrees pivot ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= m_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (CompleteColorPrefix e (i + 1 ) 0 labels ) ”
  &&  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 (i + 1 ) labels )
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full deg n_pre degrees )
) \/
(
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels_2: (@list Z)) (first: Z) (i: Z) (degrees_2: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (first = 0)) (PreH2 : ((Znth i u_data 0) = 0)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 3)) (PreH6 : (pivot = (-1))) (PreH7 : (3 <= n_pre)) (PreH8 : (n_pre <= 50)) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (m_pre <= 1225)) (PreH11 : (m_pre = (Zlength (e)))) (PreH12 : ((Zlength (u_data)) = m_pre)) (PreH13 : ((Zlength (v_data)) = m_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH15 : (Pre n_pre e )) (PreH16 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH17 : (PivotChoice n_pre degrees_2 pivot )) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : (first = 0)) (PreH21 : (CompleteColorPrefix e i first labels_2 )) ,
  TT && emp 
|--
  “ (CompleteColorPrefix e (i + 1 ) 0 (app (labels_2) ((cons (2) ((@nil Z))))) ) ”
  &&  emp
).

Definition solver_entail_wit_9_1_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels_2: (@list Z)) (first: Z) (i: Z) (degrees_2: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (first = 0)) (PreH2 : ((Znth i u_data 0) = 0)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 3)) (PreH6 : (pivot = (-1))) (PreH7 : (3 <= n_pre)) (PreH8 : (n_pre <= 50)) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (m_pre <= 1225)) (PreH11 : (m_pre = (Zlength (e)))) (PreH12 : ((Zlength (u_data)) = m_pre)) (PreH13 : ((Zlength (v_data)) = m_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH15 : (Pre n_pre e )) (PreH16 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH17 : (PivotChoice n_pre degrees_2 pivot )) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : (first = 0)) (PreH21 : (CompleteColorPrefix e i first labels_2 )) ,
  (CompleteColorPrefix e (i + 1 ) 0 (app (labels_2) ((cons (2) ((@nil Z))))) )
.

Definition solver_entail_wit_9_2 := 
(
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels_2: (@list Z)) (first: Z) (i: Z) (degrees_2: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (first <> 0)) (PreH2 : ((Znth i u_data 0) = 0)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 3)) (PreH6 : (pivot = (-1))) (PreH7 : (3 <= n_pre)) (PreH8 : (n_pre <= 50)) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (m_pre <= 1225)) (PreH11 : (m_pre = (Zlength (e)))) (PreH12 : ((Zlength (u_data)) = m_pre)) (PreH13 : ((Zlength (v_data)) = m_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH15 : (Pre n_pre e )) (PreH16 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH17 : (PivotChoice n_pre degrees_2 pivot )) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : (first = 1)) (PreH21 : (CompleteColorPrefix e i first labels_2 )) ,
  (IntArray.seg colors_pre 0 (i + 1 ) (app (labels_2) ((cons (1) ((@nil Z))))) )
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full deg n_pre degrees_2 )
|--
  EX (labels: (@list Z))  (degrees: (@list Z)) ,
  “ (deg <> 0) ” 
  &&  “ (kinds = 3) ” 
  &&  “ (pivot = (-1)) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (DegreePrefix n_pre e m_pre degrees ) ” 
  &&  “ (PivotChoice n_pre degrees pivot ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= m_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (CompleteColorPrefix e (i + 1 ) 0 labels ) ”
  &&  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 (i + 1 ) labels )
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full deg n_pre degrees )
) \/
(
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels_2: (@list Z)) (first: Z) (i: Z) (degrees_2: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (first <> 0)) (PreH2 : ((Znth i u_data 0) = 0)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 3)) (PreH6 : (pivot = (-1))) (PreH7 : (3 <= n_pre)) (PreH8 : (n_pre <= 50)) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (m_pre <= 1225)) (PreH11 : (m_pre = (Zlength (e)))) (PreH12 : ((Zlength (u_data)) = m_pre)) (PreH13 : ((Zlength (v_data)) = m_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH15 : (Pre n_pre e )) (PreH16 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH17 : (PivotChoice n_pre degrees_2 pivot )) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : (first = 1)) (PreH21 : (CompleteColorPrefix e i first labels_2 )) ,
  TT && emp 
|--
  “ (CompleteColorPrefix e (i + 1 ) 0 (app (labels_2) ((cons (1) ((@nil Z))))) ) ”
  &&  emp
).

Definition solver_entail_wit_9_2_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels_2: (@list Z)) (first: Z) (i: Z) (degrees_2: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (first <> 0)) (PreH2 : ((Znth i u_data 0) = 0)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 3)) (PreH6 : (pivot = (-1))) (PreH7 : (3 <= n_pre)) (PreH8 : (n_pre <= 50)) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (m_pre <= 1225)) (PreH11 : (m_pre = (Zlength (e)))) (PreH12 : ((Zlength (u_data)) = m_pre)) (PreH13 : ((Zlength (v_data)) = m_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH15 : (Pre n_pre e )) (PreH16 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH17 : (PivotChoice n_pre degrees_2 pivot )) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : (first = 1)) (PreH21 : (CompleteColorPrefix e i first labels_2 )) ,
  (CompleteColorPrefix e (i + 1 ) 0 (app (labels_2) ((cons (1) ((@nil Z))))) )
.

Definition solver_entail_wit_9_3 := 
(
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels_2: (@list Z)) (first: Z) (i: Z) (degrees_2: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (first <> 0)) (PreH2 : ((Znth i v_data 0) = 0)) (PreH3 : ((Znth i u_data 0) <> 0)) (PreH4 : (i < m_pre)) (PreH5 : (deg <> 0)) (PreH6 : (kinds = 3)) (PreH7 : (pivot = (-1))) (PreH8 : (3 <= n_pre)) (PreH9 : (n_pre <= 50)) (PreH10 : ((n_pre - 1 ) <= m_pre)) (PreH11 : (m_pre <= 1225)) (PreH12 : (m_pre = (Zlength (e)))) (PreH13 : ((Zlength (u_data)) = m_pre)) (PreH14 : ((Zlength (v_data)) = m_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH16 : (Pre n_pre e )) (PreH17 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH18 : (PivotChoice n_pre degrees_2 pivot )) (PreH19 : (0 <= i)) (PreH20 : (i <= m_pre)) (PreH21 : (first = 1)) (PreH22 : (CompleteColorPrefix e i first labels_2 )) ,
  (IntArray.seg colors_pre 0 (i + 1 ) (app (labels_2) ((cons (1) ((@nil Z))))) )
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full deg n_pre degrees_2 )
|--
  EX (labels: (@list Z))  (degrees: (@list Z)) ,
  “ (deg <> 0) ” 
  &&  “ (kinds = 3) ” 
  &&  “ (pivot = (-1)) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (DegreePrefix n_pre e m_pre degrees ) ” 
  &&  “ (PivotChoice n_pre degrees pivot ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= m_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (CompleteColorPrefix e (i + 1 ) 0 labels ) ”
  &&  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 (i + 1 ) labels )
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full deg n_pre degrees )
) \/
(
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels_2: (@list Z)) (first: Z) (i: Z) (degrees_2: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (first <> 0)) (PreH2 : ((Znth i v_data 0) = 0)) (PreH3 : ((Znth i u_data 0) <> 0)) (PreH4 : (i < m_pre)) (PreH5 : (deg <> 0)) (PreH6 : (kinds = 3)) (PreH7 : (pivot = (-1))) (PreH8 : (3 <= n_pre)) (PreH9 : (n_pre <= 50)) (PreH10 : ((n_pre - 1 ) <= m_pre)) (PreH11 : (m_pre <= 1225)) (PreH12 : (m_pre = (Zlength (e)))) (PreH13 : ((Zlength (u_data)) = m_pre)) (PreH14 : ((Zlength (v_data)) = m_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH16 : (Pre n_pre e )) (PreH17 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH18 : (PivotChoice n_pre degrees_2 pivot )) (PreH19 : (0 <= i)) (PreH20 : (i <= m_pre)) (PreH21 : (first = 1)) (PreH22 : (CompleteColorPrefix e i first labels_2 )) ,
  TT && emp 
|--
  “ (CompleteColorPrefix e (i + 1 ) 0 (app (labels_2) ((cons (1) ((@nil Z))))) ) ”
  &&  emp
).

Definition solver_entail_wit_9_3_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels_2: (@list Z)) (first: Z) (i: Z) (degrees_2: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (first <> 0)) (PreH2 : ((Znth i v_data 0) = 0)) (PreH3 : ((Znth i u_data 0) <> 0)) (PreH4 : (i < m_pre)) (PreH5 : (deg <> 0)) (PreH6 : (kinds = 3)) (PreH7 : (pivot = (-1))) (PreH8 : (3 <= n_pre)) (PreH9 : (n_pre <= 50)) (PreH10 : ((n_pre - 1 ) <= m_pre)) (PreH11 : (m_pre <= 1225)) (PreH12 : (m_pre = (Zlength (e)))) (PreH13 : ((Zlength (u_data)) = m_pre)) (PreH14 : ((Zlength (v_data)) = m_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH16 : (Pre n_pre e )) (PreH17 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH18 : (PivotChoice n_pre degrees_2 pivot )) (PreH19 : (0 <= i)) (PreH20 : (i <= m_pre)) (PreH21 : (first = 1)) (PreH22 : (CompleteColorPrefix e i first labels_2 )) ,
  (CompleteColorPrefix e (i + 1 ) 0 (app (labels_2) ((cons (1) ((@nil Z))))) )
.

Definition solver_entail_wit_9_4 := 
(
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels_2: (@list Z)) (first: Z) (i: Z) (degrees_2: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (first = 0)) (PreH2 : ((Znth i v_data 0) = 0)) (PreH3 : ((Znth i u_data 0) <> 0)) (PreH4 : (i < m_pre)) (PreH5 : (deg <> 0)) (PreH6 : (kinds = 3)) (PreH7 : (pivot = (-1))) (PreH8 : (3 <= n_pre)) (PreH9 : (n_pre <= 50)) (PreH10 : ((n_pre - 1 ) <= m_pre)) (PreH11 : (m_pre <= 1225)) (PreH12 : (m_pre = (Zlength (e)))) (PreH13 : ((Zlength (u_data)) = m_pre)) (PreH14 : ((Zlength (v_data)) = m_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH16 : (Pre n_pre e )) (PreH17 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH18 : (PivotChoice n_pre degrees_2 pivot )) (PreH19 : (0 <= i)) (PreH20 : (i <= m_pre)) (PreH21 : (first = 0)) (PreH22 : (CompleteColorPrefix e i first labels_2 )) ,
  (IntArray.seg colors_pre 0 (i + 1 ) (app (labels_2) ((cons (2) ((@nil Z))))) )
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full deg n_pre degrees_2 )
|--
  EX (labels: (@list Z))  (degrees: (@list Z)) ,
  “ (deg <> 0) ” 
  &&  “ (kinds = 3) ” 
  &&  “ (pivot = (-1)) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (DegreePrefix n_pre e m_pre degrees ) ” 
  &&  “ (PivotChoice n_pre degrees pivot ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= m_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (CompleteColorPrefix e (i + 1 ) 0 labels ) ”
  &&  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 (i + 1 ) labels )
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full deg n_pre degrees )
) \/
(
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels_2: (@list Z)) (first: Z) (i: Z) (degrees_2: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (first = 0)) (PreH2 : ((Znth i v_data 0) = 0)) (PreH3 : ((Znth i u_data 0) <> 0)) (PreH4 : (i < m_pre)) (PreH5 : (deg <> 0)) (PreH6 : (kinds = 3)) (PreH7 : (pivot = (-1))) (PreH8 : (3 <= n_pre)) (PreH9 : (n_pre <= 50)) (PreH10 : ((n_pre - 1 ) <= m_pre)) (PreH11 : (m_pre <= 1225)) (PreH12 : (m_pre = (Zlength (e)))) (PreH13 : ((Zlength (u_data)) = m_pre)) (PreH14 : ((Zlength (v_data)) = m_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH16 : (Pre n_pre e )) (PreH17 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH18 : (PivotChoice n_pre degrees_2 pivot )) (PreH19 : (0 <= i)) (PreH20 : (i <= m_pre)) (PreH21 : (first = 0)) (PreH22 : (CompleteColorPrefix e i first labels_2 )) ,
  TT && emp 
|--
  “ (CompleteColorPrefix e (i + 1 ) 0 (app (labels_2) ((cons (2) ((@nil Z))))) ) ”
  &&  emp
).

Definition solver_entail_wit_9_4_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels_2: (@list Z)) (first: Z) (i: Z) (degrees_2: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (first = 0)) (PreH2 : ((Znth i v_data 0) = 0)) (PreH3 : ((Znth i u_data 0) <> 0)) (PreH4 : (i < m_pre)) (PreH5 : (deg <> 0)) (PreH6 : (kinds = 3)) (PreH7 : (pivot = (-1))) (PreH8 : (3 <= n_pre)) (PreH9 : (n_pre <= 50)) (PreH10 : ((n_pre - 1 ) <= m_pre)) (PreH11 : (m_pre <= 1225)) (PreH12 : (m_pre = (Zlength (e)))) (PreH13 : ((Zlength (u_data)) = m_pre)) (PreH14 : ((Zlength (v_data)) = m_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH16 : (Pre n_pre e )) (PreH17 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH18 : (PivotChoice n_pre degrees_2 pivot )) (PreH19 : (0 <= i)) (PreH20 : (i <= m_pre)) (PreH21 : (first = 0)) (PreH22 : (CompleteColorPrefix e i first labels_2 )) ,
  (CompleteColorPrefix e (i + 1 ) 0 (app (labels_2) ((cons (2) ((@nil Z))))) )
.

Definition solver_entail_wit_9_5 := 
(
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels_2: (@list Z)) (first: Z) (i: Z) (degrees_2: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i v_data 0) <> 0)) (PreH2 : ((Znth i u_data 0) <> 0)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 3)) (PreH6 : (pivot = (-1))) (PreH7 : (3 <= n_pre)) (PreH8 : (n_pre <= 50)) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (m_pre <= 1225)) (PreH11 : (m_pre = (Zlength (e)))) (PreH12 : ((Zlength (u_data)) = m_pre)) (PreH13 : ((Zlength (v_data)) = m_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH15 : (Pre n_pre e )) (PreH16 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH17 : (PivotChoice n_pre degrees_2 pivot )) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : (first = 1)) (PreH21 : (CompleteColorPrefix e i first labels_2 )) ,
  (IntArray.seg colors_pre 0 (i + 1 ) (app (labels_2) ((cons (3) ((@nil Z))))) )
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full deg n_pre degrees_2 )
|--
  EX (labels: (@list Z))  (degrees: (@list Z)) ,
  “ (deg <> 0) ” 
  &&  “ (kinds = 3) ” 
  &&  “ (pivot = (-1)) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (DegreePrefix n_pre e m_pre degrees ) ” 
  &&  “ (PivotChoice n_pre degrees pivot ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= m_pre) ” 
  &&  “ (first = 1) ” 
  &&  “ (CompleteColorPrefix e (i + 1 ) first labels ) ”
  &&  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 (i + 1 ) labels )
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full deg n_pre degrees )
) \/
(
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels_2: (@list Z)) (first: Z) (i: Z) (degrees_2: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i v_data 0) <> 0)) (PreH2 : ((Znth i u_data 0) <> 0)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 3)) (PreH6 : (pivot = (-1))) (PreH7 : (3 <= n_pre)) (PreH8 : (n_pre <= 50)) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (m_pre <= 1225)) (PreH11 : (m_pre = (Zlength (e)))) (PreH12 : ((Zlength (u_data)) = m_pre)) (PreH13 : ((Zlength (v_data)) = m_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH15 : (Pre n_pre e )) (PreH16 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH17 : (PivotChoice n_pre degrees_2 pivot )) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : (first = 1)) (PreH21 : (CompleteColorPrefix e i first labels_2 )) ,
  TT && emp 
|--
  “ (CompleteColorPrefix e (i + 1 ) 1 (app (labels_2) ((cons (3) ((@nil Z))))) ) ”
  &&  emp
).

Definition solver_entail_wit_9_5_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels_2: (@list Z)) (first: Z) (i: Z) (degrees_2: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i v_data 0) <> 0)) (PreH2 : ((Znth i u_data 0) <> 0)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 3)) (PreH6 : (pivot = (-1))) (PreH7 : (3 <= n_pre)) (PreH8 : (n_pre <= 50)) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (m_pre <= 1225)) (PreH11 : (m_pre = (Zlength (e)))) (PreH12 : ((Zlength (u_data)) = m_pre)) (PreH13 : ((Zlength (v_data)) = m_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH15 : (Pre n_pre e )) (PreH16 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH17 : (PivotChoice n_pre degrees_2 pivot )) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : (first = 1)) (PreH21 : (CompleteColorPrefix e i first labels_2 )) ,
  (CompleteColorPrefix e (i + 1 ) 1 (app (labels_2) ((cons (3) ((@nil Z))))) )
.

Definition solver_entail_wit_9_6 := 
(
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels_2: (@list Z)) (first: Z) (i: Z) (degrees_2: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i v_data 0) <> 0)) (PreH2 : ((Znth i u_data 0) <> 0)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 3)) (PreH6 : (pivot = (-1))) (PreH7 : (3 <= n_pre)) (PreH8 : (n_pre <= 50)) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (m_pre <= 1225)) (PreH11 : (m_pre = (Zlength (e)))) (PreH12 : ((Zlength (u_data)) = m_pre)) (PreH13 : ((Zlength (v_data)) = m_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH15 : (Pre n_pre e )) (PreH16 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH17 : (PivotChoice n_pre degrees_2 pivot )) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : (first = 0)) (PreH21 : (CompleteColorPrefix e i first labels_2 )) ,
  (IntArray.seg colors_pre 0 (i + 1 ) (app (labels_2) ((cons (3) ((@nil Z))))) )
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full deg n_pre degrees_2 )
|--
  EX (labels: (@list Z))  (degrees: (@list Z)) ,
  “ (deg <> 0) ” 
  &&  “ (kinds = 3) ” 
  &&  “ (pivot = (-1)) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (DegreePrefix n_pre e m_pre degrees ) ” 
  &&  “ (PivotChoice n_pre degrees pivot ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= m_pre) ” 
  &&  “ (first = 0) ” 
  &&  “ (CompleteColorPrefix e (i + 1 ) first labels ) ”
  &&  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 (i + 1 ) labels )
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full deg n_pre degrees )
) \/
(
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels_2: (@list Z)) (first: Z) (i: Z) (degrees_2: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i v_data 0) <> 0)) (PreH2 : ((Znth i u_data 0) <> 0)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 3)) (PreH6 : (pivot = (-1))) (PreH7 : (3 <= n_pre)) (PreH8 : (n_pre <= 50)) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (m_pre <= 1225)) (PreH11 : (m_pre = (Zlength (e)))) (PreH12 : ((Zlength (u_data)) = m_pre)) (PreH13 : ((Zlength (v_data)) = m_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH15 : (Pre n_pre e )) (PreH16 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH17 : (PivotChoice n_pre degrees_2 pivot )) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : (first = 0)) (PreH21 : (CompleteColorPrefix e i first labels_2 )) ,
  TT && emp 
|--
  “ (CompleteColorPrefix e (i + 1 ) 0 (app (labels_2) ((cons (3) ((@nil Z))))) ) ”
  &&  emp
).

Definition solver_entail_wit_9_6_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels_2: (@list Z)) (first: Z) (i: Z) (degrees_2: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i v_data 0) <> 0)) (PreH2 : ((Znth i u_data 0) <> 0)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 3)) (PreH6 : (pivot = (-1))) (PreH7 : (3 <= n_pre)) (PreH8 : (n_pre <= 50)) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (m_pre <= 1225)) (PreH11 : (m_pre = (Zlength (e)))) (PreH12 : ((Zlength (u_data)) = m_pre)) (PreH13 : ((Zlength (v_data)) = m_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH15 : (Pre n_pre e )) (PreH16 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH17 : (PivotChoice n_pre degrees_2 pivot )) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : (first = 0)) (PreH21 : (CompleteColorPrefix e i first labels_2 )) ,
  (CompleteColorPrefix e (i + 1 ) 0 (app (labels_2) ((cons (3) ((@nil Z))))) )
.

Definition solver_entail_wit_10_1 := 
(
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (i: Z) (degrees_2: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i >= m_pre)) (PreH2 : (deg <> 0)) (PreH3 : (kinds = 2)) (PreH4 : (0 <= pivot)) (PreH5 : (pivot < n_pre)) (PreH6 : (3 <= n_pre)) (PreH7 : (n_pre <= 50)) (PreH8 : ((n_pre - 1 ) <= m_pre)) (PreH9 : (m_pre <= 1225)) (PreH10 : (m_pre = (Zlength (e)))) (PreH11 : ((Zlength (u_data)) = m_pre)) (PreH12 : ((Zlength (v_data)) = m_pre)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH14 : (Pre n_pre e )) (PreH15 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH16 : (PivotChoice n_pre degrees_2 pivot )) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (PivotColorPrefix e pivot i labels )) ,
  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees_2 )
|--
  EX (degrees: (@list Z))  (result: (@list Z)) ,
  “ (deg <> 0) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ (0 <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (kinds = 2) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ ((Zlength (result)) = m_pre) ” 
  &&  “ (Spec n_pre e (pair (kinds) (result)) ) ”
  &&  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full colors_pre m_pre result )
  **  (IntArray.full deg n_pre degrees )
) \/
(
forall (colors_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (i: Z) (degrees_2: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i >= m_pre)) (PreH2 : (deg <> 0)) (PreH3 : (kinds = 2)) (PreH4 : (0 <= pivot)) (PreH5 : (pivot < n_pre)) (PreH6 : (3 <= n_pre)) (PreH7 : (n_pre <= 50)) (PreH8 : ((n_pre - 1 ) <= m_pre)) (PreH9 : (m_pre <= 1225)) (PreH10 : (m_pre = (Zlength (e)))) (PreH11 : ((Zlength (u_data)) = m_pre)) (PreH12 : ((Zlength (v_data)) = m_pre)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH14 : (Pre n_pre e )) (PreH15 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH16 : (PivotChoice n_pre degrees_2 pivot )) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (PivotColorPrefix e pivot i labels )) ,
  (IntArray.seg colors_pre 0 i labels )
|--
  EX (result: (@list Z)) ,
  “ (deg <> 0) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ (0 <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (kinds = 2) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ ((Zlength (result)) = m_pre) ” 
  &&  “ (Spec n_pre e (pair (kinds) (result)) ) ”
  &&  (IntArray.full colors_pre m_pre result )
).

Definition solver_entail_wit_10_2 := 
(
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees_2: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i >= m_pre)) (PreH2 : (deg <> 0)) (PreH3 : (kinds = 3)) (PreH4 : (pivot = (-1))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : ((n_pre - 1 ) <= m_pre)) (PreH8 : (m_pre <= 1225)) (PreH9 : (m_pre = (Zlength (e)))) (PreH10 : ((Zlength (u_data)) = m_pre)) (PreH11 : ((Zlength (v_data)) = m_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH13 : (Pre n_pre e )) (PreH14 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH15 : (PivotChoice n_pre degrees_2 pivot )) (PreH16 : (0 <= i)) (PreH17 : (i <= m_pre)) (PreH18 : (first = 1)) (PreH19 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees_2 )
|--
  EX (degrees: (@list Z))  (result: (@list Z)) ,
  “ (deg <> 0) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ (pivot = (-1)) ” 
  &&  “ (kinds = 3) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ ((Zlength (result)) = m_pre) ” 
  &&  “ (Spec n_pre e (pair (kinds) (result)) ) ”
  &&  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full colors_pre m_pre result )
  **  (IntArray.full deg n_pre degrees )
) \/
(
forall (colors_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees_2: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i >= m_pre)) (PreH2 : (deg <> 0)) (PreH3 : (kinds = 3)) (PreH4 : (pivot = (-1))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : ((n_pre - 1 ) <= m_pre)) (PreH8 : (m_pre <= 1225)) (PreH9 : (m_pre = (Zlength (e)))) (PreH10 : ((Zlength (u_data)) = m_pre)) (PreH11 : ((Zlength (v_data)) = m_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH13 : (Pre n_pre e )) (PreH14 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH15 : (PivotChoice n_pre degrees_2 pivot )) (PreH16 : (0 <= i)) (PreH17 : (i <= m_pre)) (PreH18 : (first = 1)) (PreH19 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.seg colors_pre 0 i labels )
|--
  EX (result: (@list Z)) ,
  “ (deg <> 0) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ (pivot = (-1)) ” 
  &&  “ (kinds = 3) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ ((Zlength (result)) = m_pre) ” 
  &&  “ (Spec n_pre e (pair (kinds) (result)) ) ”
  &&  (IntArray.full colors_pre m_pre result )
).

Definition solver_entail_wit_10_3 := 
(
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees_2: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i >= m_pre)) (PreH2 : (deg <> 0)) (PreH3 : (kinds = 3)) (PreH4 : (pivot = (-1))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : ((n_pre - 1 ) <= m_pre)) (PreH8 : (m_pre <= 1225)) (PreH9 : (m_pre = (Zlength (e)))) (PreH10 : ((Zlength (u_data)) = m_pre)) (PreH11 : ((Zlength (v_data)) = m_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH13 : (Pre n_pre e )) (PreH14 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH15 : (PivotChoice n_pre degrees_2 pivot )) (PreH16 : (0 <= i)) (PreH17 : (i <= m_pre)) (PreH18 : (first = 0)) (PreH19 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees_2 )
|--
  EX (degrees: (@list Z))  (result: (@list Z)) ,
  “ (deg <> 0) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ (pivot = (-1)) ” 
  &&  “ (kinds = 3) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ ((Zlength (result)) = m_pre) ” 
  &&  “ (Spec n_pre e (pair (kinds) (result)) ) ”
  &&  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full colors_pre m_pre result )
  **  (IntArray.full deg n_pre degrees )
) \/
(
forall (colors_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees_2: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i >= m_pre)) (PreH2 : (deg <> 0)) (PreH3 : (kinds = 3)) (PreH4 : (pivot = (-1))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : ((n_pre - 1 ) <= m_pre)) (PreH8 : (m_pre <= 1225)) (PreH9 : (m_pre = (Zlength (e)))) (PreH10 : ((Zlength (u_data)) = m_pre)) (PreH11 : ((Zlength (v_data)) = m_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH13 : (Pre n_pre e )) (PreH14 : (DegreePrefix n_pre e m_pre degrees_2 )) (PreH15 : (PivotChoice n_pre degrees_2 pivot )) (PreH16 : (0 <= i)) (PreH17 : (i <= m_pre)) (PreH18 : (first = 0)) (PreH19 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.seg colors_pre 0 i labels )
|--
  EX (result: (@list Z)) ,
  “ (deg <> 0) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ (pivot = (-1)) ” 
  &&  “ (kinds = 3) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ ((Zlength (result)) = m_pre) ” 
  &&  “ (Spec n_pre e (pair (kinds) (result)) ) ”
  &&  (IntArray.full colors_pre m_pre result )
).

Definition solver_return_wit_1 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (result_2: (@list Z)) (deg: Z) (pivot: Z) (kinds: Z) (PreH1 : (deg <> 0)) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : (0 <= pivot)) (PreH5 : (pivot < n_pre)) (PreH6 : (kinds = 2)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : (Pre n_pre e )) (PreH11 : ((Zlength (result_2)) = m_pre)) (PreH12 : (Spec n_pre e (pair (kinds) (result_2)) )) ,
  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full colors_pre m_pre result_2 )
|--
  EX (color_count: Z)  (result: (@list Z)) ,
  “ (Spec n_pre e (pair (color_count) (result)) ) ” 
  &&  “ (kinds = color_count) ”
  &&  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full colors_pre m_pre result )
.

Definition solver_return_wit_2 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (result_2: (@list Z)) (deg: Z) (pivot: Z) (kinds: Z) (PreH1 : (deg <> 0)) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : (pivot = (-1))) (PreH5 : (kinds = 3)) (PreH6 : (m_pre = (Zlength (e)))) (PreH7 : ((Zlength (u_data)) = m_pre)) (PreH8 : ((Zlength (v_data)) = m_pre)) (PreH9 : (Pre n_pre e )) (PreH10 : ((Zlength (result_2)) = m_pre)) (PreH11 : (Spec n_pre e (pair (kinds) (result_2)) )) ,
  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full colors_pre m_pre result_2 )
|--
  EX (color_count: Z)  (result: (@list Z)) ,
  “ (Spec n_pre e (pair (color_count) (result)) ) ” 
  &&  “ (kinds = color_count) ”
  &&  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full colors_pre m_pre result )
.

Definition solver_partial_solve_wit_1_pure := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z)))  __default__Prod_Z_Z (PreH1 : (3 <= n_pre)) (PreH2 : (n_pre <= 50)) (PreH3 : ((n_pre - 1 ) <= (Zlength (e)))) (PreH4 : ((Zlength (e)) <= 1225)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (e)))) -> (((0 <= (fst ((Znth i e __default__Prod_Z_Z)))) /\ ((fst ((Znth i e __default__Prod_Z_Z))) < n_pre)) /\ ((0 <= (snd ((Znth i e __default__Prod_Z_Z)))) /\ ((snd ((Znth i e __default__Prod_Z_Z))) < n_pre))))) (PreH6 : (Pre n_pre e )) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((Znth i_2 u_data 0) = (fst ((Znth i_2 e __default__Prod_Z_Z)))) /\ ((Znth i_2 v_data 0) = (snd ((Znth i_2 e __default__Prod_Z_Z))))))) ,
  ((( &( "deg" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "colors" ) )) # Ptr  |-> colors_pre)
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre = n_pre) ” 
  &&  “ (sizeof(INT) = sizeof(INT)) ”
.

Definition solver_partial_solve_wit_1_aux := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z)))  __default__Prod_Z_Z (PreH1 : (3 <= n_pre)) (PreH2 : (n_pre <= 50)) (PreH3 : ((n_pre - 1 ) <= (Zlength (e)))) (PreH4 : ((Zlength (e)) <= 1225)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (e)))) -> (((0 <= (fst ((Znth i e __default__Prod_Z_Z)))) /\ ((fst ((Znth i e __default__Prod_Z_Z))) < n_pre)) /\ ((0 <= (snd ((Znth i e __default__Prod_Z_Z)))) /\ ((snd ((Znth i e __default__Prod_Z_Z))) < n_pre))))) (PreH6 : (Pre n_pre e )) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((Znth i_2 u_data 0) = (fst ((Znth i_2 e __default__Prod_Z_Z)))) /\ ((Znth i_2 v_data 0) = (snd ((Znth i_2 e __default__Prod_Z_Z))))))) ,
  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre = n_pre) ” 
  &&  “ (sizeof(INT) = sizeof(INT)) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= (Zlength (e))) ” 
  &&  “ ((Zlength (e)) <= 1225) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (Zlength (e)))) -> (((0 <= (fst ((Znth i e __default__Prod_Z_Z)))) /\ ((fst ((Znth i e __default__Prod_Z_Z))) < n_pre)) /\ ((0 <= (snd ((Znth i e __default__Prod_Z_Z)))) /\ ((snd ((Znth i e __default__Prod_Z_Z))) < n_pre)))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((Znth i_2 u_data 0) = (fst ((Znth i_2 e __default__Prod_Z_Z)))) /\ ((Znth i_2 v_data 0) = (snd ((Znth i_2 e __default__Prod_Z_Z)))))) ”
  &&  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees: (@list Z)) (i: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (DegreePrefix n_pre e i degrees )) (PreH15 : forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees 0)) /\ ((Znth x degrees 0) <= (2 * i ))))) ,
  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (i < m_pre) ” 
  &&  “ (deg <> 0) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (DegreePrefix n_pre e i degrees ) ” 
  &&  “ forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees 0)) /\ ((Znth x degrees 0) <= (2 * i )))) ”
  &&  (((u_pre + (i * sizeof(INT)))) # Int  |-> (Znth i u_data 0))
  **  (IntArray.missing_i u_pre i 0 m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
  **  (IntArray.full deg n_pre degrees )
.

Definition solver_partial_solve_wit_3 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees: (@list Z)) (i: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (DegreePrefix n_pre e i degrees )) (PreH15 : forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees 0)) /\ ((Znth x degrees 0) <= (2 * i ))))) ,
  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (i < m_pre) ” 
  &&  “ (deg <> 0) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (DegreePrefix n_pre e i degrees ) ” 
  &&  “ forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees 0)) /\ ((Znth x degrees 0) <= (2 * i )))) ”
  &&  (((deg + ((Znth i u_data 0) * sizeof(INT)))) # Int  |-> (Znth (Znth i u_data 0) degrees 0))
  **  (IntArray.missing_i deg (Znth i u_data 0) 0 n_pre degrees )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
.

Definition solver_partial_solve_wit_4 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees: (@list Z)) (i: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (DegreePrefix n_pre e i degrees )) (PreH15 : forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees 0)) /\ ((Znth x degrees 0) <= (2 * i ))))) ,
  (IntArray.full deg n_pre degrees )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
|--
  “ (i < m_pre) ” 
  &&  “ (deg <> 0) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (DegreePrefix n_pre e i degrees ) ” 
  &&  “ forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees 0)) /\ ((Znth x degrees 0) <= (2 * i )))) ”
  &&  (((deg + ((Znth i u_data 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i deg (Znth i u_data 0) 0 n_pre degrees )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
.

Definition solver_partial_solve_wit_5 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees: (@list Z)) (i: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (DegreePrefix n_pre e i degrees )) (PreH15 : forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees 0)) /\ ((Znth x degrees 0) <= (2 * i ))))) ,
  (IntArray.full deg n_pre (replace_Znth ((Znth i u_data 0)) (((Znth (Znth i u_data 0) degrees 0) + 1 )) (degrees)) )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
|--
  “ (i < m_pre) ” 
  &&  “ (deg <> 0) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (DegreePrefix n_pre e i degrees ) ” 
  &&  “ forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees 0)) /\ ((Znth x degrees 0) <= (2 * i )))) ”
  &&  (((v_pre + (i * sizeof(INT)))) # Int  |-> (Znth i v_data 0))
  **  (IntArray.missing_i v_pre i 0 m_pre v_data )
  **  (IntArray.full deg n_pre (replace_Znth ((Znth i u_data 0)) (((Znth (Znth i u_data 0) degrees 0) + 1 )) (degrees)) )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.undef_full colors_pre m_pre )
.

Definition solver_partial_solve_wit_6 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees: (@list Z)) (i: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (DegreePrefix n_pre e i degrees )) (PreH15 : forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees 0)) /\ ((Znth x degrees 0) <= (2 * i ))))) ,
  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full deg n_pre (replace_Znth ((Znth i u_data 0)) (((Znth (Znth i u_data 0) degrees 0) + 1 )) (degrees)) )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.undef_full colors_pre m_pre )
|--
  “ (i < m_pre) ” 
  &&  “ (deg <> 0) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (DegreePrefix n_pre e i degrees ) ” 
  &&  “ forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees 0)) /\ ((Znth x degrees 0) <= (2 * i )))) ”
  &&  (((deg + ((Znth i v_data 0) * sizeof(INT)))) # Int  |-> (Znth (Znth i v_data 0) (replace_Znth ((Znth i u_data 0)) (((Znth (Znth i u_data 0) degrees 0) + 1 )) (degrees)) 0))
  **  (IntArray.missing_i deg (Znth i v_data 0) 0 n_pre (replace_Znth ((Znth i u_data 0)) (((Znth (Znth i u_data 0) degrees 0) + 1 )) (degrees)) )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.undef_full colors_pre m_pre )
.

Definition solver_partial_solve_wit_7 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees: (@list Z)) (i: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (deg <> 0)) (PreH3 : (3 <= n_pre)) (PreH4 : (n_pre <= 50)) (PreH5 : ((n_pre - 1 ) <= m_pre)) (PreH6 : (m_pre <= 1225)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH11 : (Pre n_pre e )) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (DegreePrefix n_pre e i degrees )) (PreH15 : forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees 0)) /\ ((Znth x degrees 0) <= (2 * i ))))) ,
  (IntArray.full deg n_pre (replace_Znth ((Znth i u_data 0)) (((Znth (Znth i u_data 0) degrees 0) + 1 )) (degrees)) )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.undef_full colors_pre m_pre )
|--
  “ (i < m_pre) ” 
  &&  “ (deg <> 0) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (DegreePrefix n_pre e i degrees ) ” 
  &&  “ forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees 0)) /\ ((Znth x degrees 0) <= (2 * i )))) ”
  &&  (((deg + ((Znth i v_data 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i deg (Znth i v_data 0) 0 n_pre (replace_Znth ((Znth i u_data 0)) (((Znth (Znth i u_data 0) degrees 0) + 1 )) (degrees)) )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.undef_full colors_pre m_pre )
.

Definition solver_partial_solve_wit_8 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees: (@list Z)) (i: Z) (pivot: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (deg <> 0)) (PreH3 : (pivot = (-1))) (PreH4 : (3 <= n_pre)) (PreH5 : (n_pre <= 50)) (PreH6 : ((n_pre - 1 ) <= m_pre)) (PreH7 : (m_pre <= 1225)) (PreH8 : (m_pre = (Zlength (e)))) (PreH9 : ((Zlength (u_data)) = m_pre)) (PreH10 : ((Zlength (v_data)) = m_pre)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH12 : (Pre n_pre e )) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (DegreePrefix n_pre e m_pre degrees )) (PreH16 : (PivotPrefix n_pre degrees i )) (PreH17 : forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees 0)) /\ ((Znth x degrees 0) <= (n_pre - 1 ))))) ,
  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (i < n_pre) ” 
  &&  “ (deg <> 0) ” 
  &&  “ (pivot = (-1)) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (DegreePrefix n_pre e m_pre degrees ) ” 
  &&  “ (PivotPrefix n_pre degrees i ) ” 
  &&  “ forall (x: Z) , (((0 <= x) /\ (x < n_pre)) -> ((0 <= (Znth x degrees 0)) /\ ((Znth x degrees 0) <= (n_pre - 1 )))) ”
  &&  (((deg + (i * sizeof(INT)))) # Int  |-> (Znth i degrees 0))
  **  (IntArray.missing_i deg i 0 n_pre degrees )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.undef_full colors_pre m_pre )
.

Definition solver_partial_solve_wit_9 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (deg <> 0)) (PreH3 : (kinds = 2)) (PreH4 : (0 <= pivot)) (PreH5 : (pivot < n_pre)) (PreH6 : (3 <= n_pre)) (PreH7 : (n_pre <= 50)) (PreH8 : ((n_pre - 1 ) <= m_pre)) (PreH9 : (m_pre <= 1225)) (PreH10 : (m_pre = (Zlength (e)))) (PreH11 : ((Zlength (u_data)) = m_pre)) (PreH12 : ((Zlength (v_data)) = m_pre)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH14 : (Pre n_pre e )) (PreH15 : (DegreePrefix n_pre e m_pre degrees )) (PreH16 : (PivotChoice n_pre degrees pivot )) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (PivotColorPrefix e pivot i labels )) ,
  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (i < m_pre) ” 
  &&  “ (deg <> 0) ” 
  &&  “ (kinds = 2) ” 
  &&  “ (0 <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (DegreePrefix n_pre e m_pre degrees ) ” 
  &&  “ (PivotChoice n_pre degrees pivot ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (PivotColorPrefix e pivot i labels ) ”
  &&  (((u_pre + (i * sizeof(INT)))) # Int  |-> (Znth i u_data 0))
  **  (IntArray.missing_i u_pre i 0 m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
.

Definition solver_partial_solve_wit_10 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i u_data 0) <> pivot)) (PreH2 : (i < m_pre)) (PreH3 : (deg <> 0)) (PreH4 : (kinds = 2)) (PreH5 : (0 <= pivot)) (PreH6 : (pivot < n_pre)) (PreH7 : (3 <= n_pre)) (PreH8 : (n_pre <= 50)) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (m_pre <= 1225)) (PreH11 : (m_pre = (Zlength (e)))) (PreH12 : ((Zlength (u_data)) = m_pre)) (PreH13 : ((Zlength (v_data)) = m_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH15 : (Pre n_pre e )) (PreH16 : (DegreePrefix n_pre e m_pre degrees )) (PreH17 : (PivotChoice n_pre degrees pivot )) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : (PivotColorPrefix e pivot i labels )) ,
  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ ((Znth i u_data 0) <> pivot) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (deg <> 0) ” 
  &&  “ (kinds = 2) ” 
  &&  “ (0 <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (DegreePrefix n_pre e m_pre degrees ) ” 
  &&  “ (PivotChoice n_pre degrees pivot ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (PivotColorPrefix e pivot i labels ) ”
  &&  (((v_pre + (i * sizeof(INT)))) # Int  |-> (Znth i v_data 0))
  **  (IntArray.missing_i v_pre i 0 m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
.

Definition solver_partial_solve_wit_11 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i v_data 0) = pivot)) (PreH2 : ((Znth i u_data 0) <> pivot)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 2)) (PreH6 : (0 <= pivot)) (PreH7 : (pivot < n_pre)) (PreH8 : (3 <= n_pre)) (PreH9 : (n_pre <= 50)) (PreH10 : ((n_pre - 1 ) <= m_pre)) (PreH11 : (m_pre <= 1225)) (PreH12 : (m_pre = (Zlength (e)))) (PreH13 : ((Zlength (u_data)) = m_pre)) (PreH14 : ((Zlength (v_data)) = m_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH16 : (Pre n_pre e )) (PreH17 : (DegreePrefix n_pre e m_pre degrees )) (PreH18 : (PivotChoice n_pre degrees pivot )) (PreH19 : (0 <= i)) (PreH20 : (i <= m_pre)) (PreH21 : (PivotColorPrefix e pivot i labels )) ,
  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ ((Znth i v_data 0) = pivot) ” 
  &&  “ ((Znth i u_data 0) <> pivot) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (deg <> 0) ” 
  &&  “ (kinds = 2) ” 
  &&  “ (0 <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (DegreePrefix n_pre e m_pre degrees ) ” 
  &&  “ (PivotChoice n_pre degrees pivot ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (PivotColorPrefix e pivot i labels ) ”
  &&  (((colors_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.full deg n_pre degrees )
.

Definition solver_partial_solve_wit_12 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i u_data 0) = pivot)) (PreH2 : (i < m_pre)) (PreH3 : (deg <> 0)) (PreH4 : (kinds = 2)) (PreH5 : (0 <= pivot)) (PreH6 : (pivot < n_pre)) (PreH7 : (3 <= n_pre)) (PreH8 : (n_pre <= 50)) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (m_pre <= 1225)) (PreH11 : (m_pre = (Zlength (e)))) (PreH12 : ((Zlength (u_data)) = m_pre)) (PreH13 : ((Zlength (v_data)) = m_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH15 : (Pre n_pre e )) (PreH16 : (DegreePrefix n_pre e m_pre degrees )) (PreH17 : (PivotChoice n_pre degrees pivot )) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : (PivotColorPrefix e pivot i labels )) ,
  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ ((Znth i u_data 0) = pivot) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (deg <> 0) ” 
  &&  “ (kinds = 2) ” 
  &&  “ (0 <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (DegreePrefix n_pre e m_pre degrees ) ” 
  &&  “ (PivotChoice n_pre degrees pivot ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (PivotColorPrefix e pivot i labels ) ”
  &&  (((colors_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.full deg n_pre degrees )
.

Definition solver_partial_solve_wit_13 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i v_data 0) <> pivot)) (PreH2 : ((Znth i u_data 0) <> pivot)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 2)) (PreH6 : (0 <= pivot)) (PreH7 : (pivot < n_pre)) (PreH8 : (3 <= n_pre)) (PreH9 : (n_pre <= 50)) (PreH10 : ((n_pre - 1 ) <= m_pre)) (PreH11 : (m_pre <= 1225)) (PreH12 : (m_pre = (Zlength (e)))) (PreH13 : ((Zlength (u_data)) = m_pre)) (PreH14 : ((Zlength (v_data)) = m_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH16 : (Pre n_pre e )) (PreH17 : (DegreePrefix n_pre e m_pre degrees )) (PreH18 : (PivotChoice n_pre degrees pivot )) (PreH19 : (0 <= i)) (PreH20 : (i <= m_pre)) (PreH21 : (PivotColorPrefix e pivot i labels )) ,
  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ ((Znth i v_data 0) <> pivot) ” 
  &&  “ ((Znth i u_data 0) <> pivot) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (deg <> 0) ” 
  &&  “ (kinds = 2) ” 
  &&  “ (0 <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (DegreePrefix n_pre e m_pre degrees ) ” 
  &&  “ (PivotChoice n_pre degrees pivot ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (PivotColorPrefix e pivot i labels ) ”
  &&  (((colors_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.full deg n_pre degrees )
.

Definition solver_partial_solve_wit_14 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (deg <> 0)) (PreH3 : (kinds = 3)) (PreH4 : (pivot = (-1))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : ((n_pre - 1 ) <= m_pre)) (PreH8 : (m_pre <= 1225)) (PreH9 : (m_pre = (Zlength (e)))) (PreH10 : ((Zlength (u_data)) = m_pre)) (PreH11 : ((Zlength (v_data)) = m_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH13 : (Pre n_pre e )) (PreH14 : (DegreePrefix n_pre e m_pre degrees )) (PreH15 : (PivotChoice n_pre degrees pivot )) (PreH16 : (0 <= i)) (PreH17 : (i <= m_pre)) (PreH18 : (first = 1)) (PreH19 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (i < m_pre) ” 
  &&  “ (deg <> 0) ” 
  &&  “ (kinds = 3) ” 
  &&  “ (pivot = (-1)) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (DegreePrefix n_pre e m_pre degrees ) ” 
  &&  “ (PivotChoice n_pre degrees pivot ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (first = 1) ” 
  &&  “ (CompleteColorPrefix e i first labels ) ”
  &&  (((u_pre + (i * sizeof(INT)))) # Int  |-> (Znth i u_data 0))
  **  (IntArray.missing_i u_pre i 0 m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
.

Definition solver_partial_solve_wit_15 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (deg <> 0)) (PreH3 : (kinds = 3)) (PreH4 : (pivot = (-1))) (PreH5 : (3 <= n_pre)) (PreH6 : (n_pre <= 50)) (PreH7 : ((n_pre - 1 ) <= m_pre)) (PreH8 : (m_pre <= 1225)) (PreH9 : (m_pre = (Zlength (e)))) (PreH10 : ((Zlength (u_data)) = m_pre)) (PreH11 : ((Zlength (v_data)) = m_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH13 : (Pre n_pre e )) (PreH14 : (DegreePrefix n_pre e m_pre degrees )) (PreH15 : (PivotChoice n_pre degrees pivot )) (PreH16 : (0 <= i)) (PreH17 : (i <= m_pre)) (PreH18 : (first = 0)) (PreH19 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (i < m_pre) ” 
  &&  “ (deg <> 0) ” 
  &&  “ (kinds = 3) ” 
  &&  “ (pivot = (-1)) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (DegreePrefix n_pre e m_pre degrees ) ” 
  &&  “ (PivotChoice n_pre degrees pivot ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (first = 0) ” 
  &&  “ (CompleteColorPrefix e i first labels ) ”
  &&  (((u_pre + (i * sizeof(INT)))) # Int  |-> (Znth i u_data 0))
  **  (IntArray.missing_i u_pre i 0 m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
.

Definition solver_partial_solve_wit_16 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i u_data 0) <> 0)) (PreH2 : (i < m_pre)) (PreH3 : (deg <> 0)) (PreH4 : (kinds = 3)) (PreH5 : (pivot = (-1))) (PreH6 : (3 <= n_pre)) (PreH7 : (n_pre <= 50)) (PreH8 : ((n_pre - 1 ) <= m_pre)) (PreH9 : (m_pre <= 1225)) (PreH10 : (m_pre = (Zlength (e)))) (PreH11 : ((Zlength (u_data)) = m_pre)) (PreH12 : ((Zlength (v_data)) = m_pre)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH14 : (Pre n_pre e )) (PreH15 : (DegreePrefix n_pre e m_pre degrees )) (PreH16 : (PivotChoice n_pre degrees pivot )) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (first = 0)) (PreH20 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ ((Znth i u_data 0) <> 0) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (deg <> 0) ” 
  &&  “ (kinds = 3) ” 
  &&  “ (pivot = (-1)) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (DegreePrefix n_pre e m_pre degrees ) ” 
  &&  “ (PivotChoice n_pre degrees pivot ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (first = 0) ” 
  &&  “ (CompleteColorPrefix e i first labels ) ”
  &&  (((v_pre + (i * sizeof(INT)))) # Int  |-> (Znth i v_data 0))
  **  (IntArray.missing_i v_pre i 0 m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
.

Definition solver_partial_solve_wit_17 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i u_data 0) <> 0)) (PreH2 : (i < m_pre)) (PreH3 : (deg <> 0)) (PreH4 : (kinds = 3)) (PreH5 : (pivot = (-1))) (PreH6 : (3 <= n_pre)) (PreH7 : (n_pre <= 50)) (PreH8 : ((n_pre - 1 ) <= m_pre)) (PreH9 : (m_pre <= 1225)) (PreH10 : (m_pre = (Zlength (e)))) (PreH11 : ((Zlength (u_data)) = m_pre)) (PreH12 : ((Zlength (v_data)) = m_pre)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH14 : (Pre n_pre e )) (PreH15 : (DegreePrefix n_pre e m_pre degrees )) (PreH16 : (PivotChoice n_pre degrees pivot )) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (first = 1)) (PreH20 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ ((Znth i u_data 0) <> 0) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (deg <> 0) ” 
  &&  “ (kinds = 3) ” 
  &&  “ (pivot = (-1)) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (DegreePrefix n_pre e m_pre degrees ) ” 
  &&  “ (PivotChoice n_pre degrees pivot ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (first = 1) ” 
  &&  “ (CompleteColorPrefix e i first labels ) ”
  &&  (((v_pre + (i * sizeof(INT)))) # Int  |-> (Znth i v_data 0))
  **  (IntArray.missing_i v_pre i 0 m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
.

Definition solver_partial_solve_wit_18 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (first = 0)) (PreH2 : ((Znth i u_data 0) = 0)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 3)) (PreH6 : (pivot = (-1))) (PreH7 : (3 <= n_pre)) (PreH8 : (n_pre <= 50)) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (m_pre <= 1225)) (PreH11 : (m_pre = (Zlength (e)))) (PreH12 : ((Zlength (u_data)) = m_pre)) (PreH13 : ((Zlength (v_data)) = m_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH15 : (Pre n_pre e )) (PreH16 : (DegreePrefix n_pre e m_pre degrees )) (PreH17 : (PivotChoice n_pre degrees pivot )) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : (first = 0)) (PreH21 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (first = 0) ” 
  &&  “ ((Znth i u_data 0) = 0) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (deg <> 0) ” 
  &&  “ (kinds = 3) ” 
  &&  “ (pivot = (-1)) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (DegreePrefix n_pre e m_pre degrees ) ” 
  &&  “ (PivotChoice n_pre degrees pivot ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (first = 0) ” 
  &&  “ (CompleteColorPrefix e i first labels ) ”
  &&  (((colors_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.full deg n_pre degrees )
.

Definition solver_partial_solve_wit_19 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (first <> 0)) (PreH2 : ((Znth i u_data 0) = 0)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 3)) (PreH6 : (pivot = (-1))) (PreH7 : (3 <= n_pre)) (PreH8 : (n_pre <= 50)) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (m_pre <= 1225)) (PreH11 : (m_pre = (Zlength (e)))) (PreH12 : ((Zlength (u_data)) = m_pre)) (PreH13 : ((Zlength (v_data)) = m_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH15 : (Pre n_pre e )) (PreH16 : (DegreePrefix n_pre e m_pre degrees )) (PreH17 : (PivotChoice n_pre degrees pivot )) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : (first = 1)) (PreH21 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (first <> 0) ” 
  &&  “ ((Znth i u_data 0) = 0) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (deg <> 0) ” 
  &&  “ (kinds = 3) ” 
  &&  “ (pivot = (-1)) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (DegreePrefix n_pre e m_pre degrees ) ” 
  &&  “ (PivotChoice n_pre degrees pivot ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (first = 1) ” 
  &&  “ (CompleteColorPrefix e i first labels ) ”
  &&  (((colors_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.full deg n_pre degrees )
.

Definition solver_partial_solve_wit_20 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (first <> 0)) (PreH2 : ((Znth i v_data 0) = 0)) (PreH3 : ((Znth i u_data 0) <> 0)) (PreH4 : (i < m_pre)) (PreH5 : (deg <> 0)) (PreH6 : (kinds = 3)) (PreH7 : (pivot = (-1))) (PreH8 : (3 <= n_pre)) (PreH9 : (n_pre <= 50)) (PreH10 : ((n_pre - 1 ) <= m_pre)) (PreH11 : (m_pre <= 1225)) (PreH12 : (m_pre = (Zlength (e)))) (PreH13 : ((Zlength (u_data)) = m_pre)) (PreH14 : ((Zlength (v_data)) = m_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH16 : (Pre n_pre e )) (PreH17 : (DegreePrefix n_pre e m_pre degrees )) (PreH18 : (PivotChoice n_pre degrees pivot )) (PreH19 : (0 <= i)) (PreH20 : (i <= m_pre)) (PreH21 : (first = 1)) (PreH22 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (first <> 0) ” 
  &&  “ ((Znth i v_data 0) = 0) ” 
  &&  “ ((Znth i u_data 0) <> 0) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (deg <> 0) ” 
  &&  “ (kinds = 3) ” 
  &&  “ (pivot = (-1)) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (DegreePrefix n_pre e m_pre degrees ) ” 
  &&  “ (PivotChoice n_pre degrees pivot ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (first = 1) ” 
  &&  “ (CompleteColorPrefix e i first labels ) ”
  &&  (((colors_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.full deg n_pre degrees )
.

Definition solver_partial_solve_wit_21 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : (first = 0)) (PreH2 : ((Znth i v_data 0) = 0)) (PreH3 : ((Znth i u_data 0) <> 0)) (PreH4 : (i < m_pre)) (PreH5 : (deg <> 0)) (PreH6 : (kinds = 3)) (PreH7 : (pivot = (-1))) (PreH8 : (3 <= n_pre)) (PreH9 : (n_pre <= 50)) (PreH10 : ((n_pre - 1 ) <= m_pre)) (PreH11 : (m_pre <= 1225)) (PreH12 : (m_pre = (Zlength (e)))) (PreH13 : ((Zlength (u_data)) = m_pre)) (PreH14 : ((Zlength (v_data)) = m_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH16 : (Pre n_pre e )) (PreH17 : (DegreePrefix n_pre e m_pre degrees )) (PreH18 : (PivotChoice n_pre degrees pivot )) (PreH19 : (0 <= i)) (PreH20 : (i <= m_pre)) (PreH21 : (first = 0)) (PreH22 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (first = 0) ” 
  &&  “ ((Znth i v_data 0) = 0) ” 
  &&  “ ((Znth i u_data 0) <> 0) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (deg <> 0) ” 
  &&  “ (kinds = 3) ” 
  &&  “ (pivot = (-1)) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (DegreePrefix n_pre e m_pre degrees ) ” 
  &&  “ (PivotChoice n_pre degrees pivot ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (first = 0) ” 
  &&  “ (CompleteColorPrefix e i first labels ) ”
  &&  (((colors_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.full deg n_pre degrees )
.

Definition solver_partial_solve_wit_22 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i v_data 0) <> 0)) (PreH2 : ((Znth i u_data 0) <> 0)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 3)) (PreH6 : (pivot = (-1))) (PreH7 : (3 <= n_pre)) (PreH8 : (n_pre <= 50)) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (m_pre <= 1225)) (PreH11 : (m_pre = (Zlength (e)))) (PreH12 : ((Zlength (u_data)) = m_pre)) (PreH13 : ((Zlength (v_data)) = m_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH15 : (Pre n_pre e )) (PreH16 : (DegreePrefix n_pre e m_pre degrees )) (PreH17 : (PivotChoice n_pre degrees pivot )) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : (first = 1)) (PreH21 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ ((Znth i v_data 0) <> 0) ” 
  &&  “ ((Znth i u_data 0) <> 0) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (deg <> 0) ” 
  &&  “ (kinds = 3) ” 
  &&  “ (pivot = (-1)) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (DegreePrefix n_pre e m_pre degrees ) ” 
  &&  “ (PivotChoice n_pre degrees pivot ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (first = 1) ” 
  &&  “ (CompleteColorPrefix e i first labels ) ”
  &&  (((colors_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.full deg n_pre degrees )
.

Definition solver_partial_solve_wit_23 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (labels: (@list Z)) (first: Z) (i: Z) (degrees: (@list Z)) (pivot: Z) (kinds: Z) (deg: Z)  __default__Prod_Z_Z (PreH1 : ((Znth i v_data 0) <> 0)) (PreH2 : ((Znth i u_data 0) <> 0)) (PreH3 : (i < m_pre)) (PreH4 : (deg <> 0)) (PreH5 : (kinds = 3)) (PreH6 : (pivot = (-1))) (PreH7 : (3 <= n_pre)) (PreH8 : (n_pre <= 50)) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (m_pre <= 1225)) (PreH11 : (m_pre = (Zlength (e)))) (PreH12 : ((Zlength (u_data)) = m_pre)) (PreH13 : ((Zlength (v_data)) = m_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z))))))) (PreH15 : (Pre n_pre e )) (PreH16 : (DegreePrefix n_pre e m_pre degrees )) (PreH17 : (PivotChoice n_pre degrees pivot )) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : (first = 0)) (PreH21 : (CompleteColorPrefix e i first labels )) ,
  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.undef_seg colors_pre i m_pre )
  **  (IntArray.full deg n_pre degrees )
|--
  “ ((Znth i v_data 0) <> 0) ” 
  &&  “ ((Znth i u_data 0) <> 0) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (deg <> 0) ” 
  &&  “ (kinds = 3) ” 
  &&  “ (pivot = (-1)) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (m_pre <= 1225) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m_pre)) -> (((((0 <= (Znth k u_data 0)) /\ ((Znth k u_data 0) < n_pre)) /\ ((0 <= (Znth k v_data 0)) /\ ((Znth k v_data 0) < n_pre))) /\ ((Znth k u_data 0) = (fst ((Znth k e __default__Prod_Z_Z))))) /\ ((Znth k v_data 0) = (snd ((Znth k e __default__Prod_Z_Z)))))) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ (DegreePrefix n_pre e m_pre degrees ) ” 
  &&  “ (PivotChoice n_pre degrees pivot ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (first = 0) ” 
  &&  “ (CompleteColorPrefix e i first labels ) ”
  &&  (((colors_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg colors_pre (i + 1 ) m_pre )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.seg colors_pre 0 i labels )
  **  (IntArray.full deg n_pre degrees )
.

Definition solver_partial_solve_wit_24 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees: (@list Z)) (result: (@list Z)) (deg: Z) (pivot: Z) (kinds: Z) (PreH1 : (deg <> 0)) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : (0 <= pivot)) (PreH5 : (pivot < n_pre)) (PreH6 : (kinds = 2)) (PreH7 : (m_pre = (Zlength (e)))) (PreH8 : ((Zlength (u_data)) = m_pre)) (PreH9 : ((Zlength (v_data)) = m_pre)) (PreH10 : (Pre n_pre e )) (PreH11 : ((Zlength (result)) = m_pre)) (PreH12 : (Spec n_pre e (pair (kinds) (result)) )) ,
  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full colors_pre m_pre result )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (deg <> 0) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ (0 <= pivot) ” 
  &&  “ (pivot < n_pre) ” 
  &&  “ (kinds = 2) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ ((Zlength (result)) = m_pre) ” 
  &&  “ (Spec n_pre e (pair (kinds) (result)) ) ”
  &&  (IntArray.full deg n_pre degrees )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full colors_pre m_pre result )
.

Definition solver_partial_solve_wit_25 := 
forall (colors_pre: Z) (v_pre: Z) (u_pre: Z) (m_pre: Z) (n_pre: Z) (v_data: (@list Z)) (u_data: (@list Z)) (e: (@list (Z * Z))) (degrees: (@list Z)) (result: (@list Z)) (deg: Z) (pivot: Z) (kinds: Z) (PreH1 : (deg <> 0)) (PreH2 : (3 <= n_pre)) (PreH3 : (n_pre <= 50)) (PreH4 : (pivot = (-1))) (PreH5 : (kinds = 3)) (PreH6 : (m_pre = (Zlength (e)))) (PreH7 : ((Zlength (u_data)) = m_pre)) (PreH8 : ((Zlength (v_data)) = m_pre)) (PreH9 : (Pre n_pre e )) (PreH10 : ((Zlength (result)) = m_pre)) (PreH11 : (Spec n_pre e (pair (kinds) (result)) )) ,
  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full colors_pre m_pre result )
  **  (IntArray.full deg n_pre degrees )
|--
  “ (deg <> 0) ” 
  &&  “ (3 <= n_pre) ” 
  &&  “ (n_pre <= 50) ” 
  &&  “ (pivot = (-1)) ” 
  &&  “ (kinds = 3) ” 
  &&  “ (m_pre = (Zlength (e))) ” 
  &&  “ ((Zlength (u_data)) = m_pre) ” 
  &&  “ ((Zlength (v_data)) = m_pre) ” 
  &&  “ (Pre n_pre e ) ” 
  &&  “ ((Zlength (result)) = m_pre) ” 
  &&  “ (Spec n_pre e (pair (kinds) (result)) ) ”
  &&  (IntArray.full deg n_pre degrees )
  **  (IntArray.full u_pre m_pre u_data )
  **  (IntArray.full v_pre m_pre v_data )
  **  (IntArray.full colors_pre m_pre result )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Axiom proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Axiom proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Axiom proof_of_solver_entail_wit_7_3 : solver_entail_wit_7_3.
Axiom proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Axiom proof_of_solver_entail_wit_9_1 : solver_entail_wit_9_1.
Axiom proof_of_solver_entail_wit_9_2 : solver_entail_wit_9_2.
Axiom proof_of_solver_entail_wit_9_3 : solver_entail_wit_9_3.
Axiom proof_of_solver_entail_wit_9_4 : solver_entail_wit_9_4.
Axiom proof_of_solver_entail_wit_9_5 : solver_entail_wit_9_5.
Axiom proof_of_solver_entail_wit_9_6 : solver_entail_wit_9_6.
Axiom proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1.
Axiom proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2.
Axiom proof_of_solver_entail_wit_10_3 : solver_entail_wit_10_3.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
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
Axiom proof_of_solver_partial_solve_wit_25 : solver_partial_solve_wit_25.

End VC_Correct.
